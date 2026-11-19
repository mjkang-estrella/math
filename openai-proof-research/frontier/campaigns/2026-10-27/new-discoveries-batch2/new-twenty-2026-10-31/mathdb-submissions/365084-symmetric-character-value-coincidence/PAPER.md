# Clusters of symmetric-group characters agreeing on bounded support

## Statement

Let \(X\) be a finite set of pairs \((m,x)\) with \(x\in S_m\), and let \(k\ge1\) be an integer. There is an \(N\) at least as large as every arity in \(X\) such that for every \(n\ge N\) there are \(k\) distinct irreducible complex characters of \(S_n\) whose values agree on every \(g\in S_n\) having the full cycle type of some \(x\in X\) extended by \(n-m\) fixed points. Full cycle type includes all one-cycles. This is the stable formulation of MathDB 365084 and Craven's Conjecture 3.5. The tests and \(k\) are fixed before \(N\). The family may depend on \(n\).

We prove the following stronger assertion. For every \(d\ge0\) and \(k\ge1\), for each \(n\) above an explicit bound \(U(d,k)\), there are \(k\) distinct irreducible complex characters of \(S_n\) agreeing on every permutation moving at most \(d\) letters. The indexing partitions can be chosen with equal hook multisets. Set \(r=2(d+1)\), \(L=2^r\), \(E=L+2\), and \(M=E+1\). Define \(D=E\sum_{j=0}^{k-1} M^j\), \(a=D+1\), and \(b=2a+1\). We may take
\[
U(d,k)=D^2+(a+b)a+Db .
\]
For the finite tests take \(d\) to be the largest arity, or zero for an empty set, and \(N=\max(d,U(d,k))\).

## Character values from finitely many moments

Use the classical classification of irreducible complex \(S_n\)-representations by partitions of \(n\), the Frobenius character formula, and the Schur alternant formula. For a partition \(\lambda\) with \(\ell\) positive parts write \(b_i=\lambda_i+\ell-i\), \(1\le i\le\ell\), and \(\Delta(b)=\prod_{i<j}(b_i-b_j)\). These beta numbers are positive and strictly decreasing. Write \(u^{\underline t}=u(u-1)\cdots(u-t+1)\), with empty product 1.

Let \(\rho=(\rho_1,\ldots,\rho_s)\) list the indexed nontrivial cycles of a permutation moving \(q\) letters, so \(\sum_j\rho_j=q\). Let \(p_j=\sum_i x_i^j\) in \(\ell\) variables. The Frobenius formula expands \(p_1^{n-q}\prod_j p_{\rho_j}\) as \(\sum_{\mu\vdash n}\chi^\mu(\rho\,1^{n-q})s_\mu\). Multiply by \(\det(x_i^{\ell-j})\) and extract the coefficient at \(x_1^{b_1}\cdots x_\ell^{b_\ell}\). Schur polynomials of length greater than \(\ell\) vanish in these variables. For each remaining \(\mu\), its alternant permutes its shifted parts. The strictly decreasing exponent tuple selects \(\lambda\) and the identity term with sign \(+1\).

Assign each indexed cycle \(j\) to a variable \(i\), and let \(s_i\) be the sum of the lengths assigned to \(i\). Repeated cycle lengths still give separately indexed choices. The multinomial expansion yields a contribution
\[
(n-q)!\det_{i,j}\!\frac{1}{(b_i-s_i-\ell+j)!}
=\frac{(n-q)!}{\prod_i b_i!}\,\Delta(b-s)\prod_i b_i^{\underline{s_i}}.
\]
A reciprocal negative factorial means zero. If \(b_i<s_i\) the corresponding row and falling factorial vanish. Otherwise multiplication by the row factorial \((b_i-s_i)!\) gives a determinant of monic falling factorials in descending degrees, which equals \(\Delta(b-s)\) by triangular change of basis. At \(q=0\) the sole assignment gives \(\chi^\lambda(1)=n!\Delta(b)/\prod_i b_i!\).

Consequently \((n)^{\underline q}\chi^\lambda(\rho\,1^{n-q})/\chi^\lambda(1)\) equals
\[
\frac{\sum_{\text{assignments}}\Delta(b-s)\prod_i b_i^{\underline{s_i}}}{\Delta(b)} .
\]
The numerator changes sign when two beta variables exchange, since the exchange relabels assignments and reverses the Vandermonde sign. Each distinct diagonal linear factor divides it over \(\mathbb Q\), hence so does their product. The quotient is symmetric and has degree at most \(q\). The fundamental theorem of symmetric polynomials, applied in each homogeneous degree with \(\deg e_j=j\), and Newton's identities express it using only the power sums of degrees through \(q\). Thus at common \(n,\ell\), common beta moments through \(d\) and common degree give common actual character values at every type of support at most \(d\). This includes the identity and types with repeated or multiple nontrivial cycles. The bounded-degree principle also follows from the shifted Schur formulas of Okounkov and Olshanski.

## Boundary polynomials

A finite subset \(B\) of the positive integers gives
\[
W(z)=\sum_{t\in B}z^t,\qquad A(z)=1+(z-1)W(z).
\]
Each maximal occupied interval \([u,v-1]\) contributes \(z^v-z^u\). The boundary polynomials are exactly those starting at exponent zero with nonzero coefficients \(+1,-1,+1,\ldots,+1\) in increasing order. Pair each negative coefficient with the next positive one to recover the occupied intervals. Sorting the occupied positions \(b_1>\cdots>b_\ell>0\) and subtracting the staircase gives the partition \(\lambda_i=b_i-\ell+i\). These maps are inverse, including the constant polynomial and the empty partition.

For a nonempty partition, put \(a_j=\ell+j-1-\lambda'_j\) for \(1\le j\le\lambda_1\). These strictly increase. The difference \(b_i-a_j=\lambda_i-j+\lambda'_j-i+1\) is positive at cells, where it is the hook length, and negative at noncells, where both row and column differences are at most \(-1\). Thus the \(a_j\) are distinct holes. They lie in \([0,b_1]\) and exhaust the holes there because \(\lambda_1+\ell=b_1+1\). Hook lengths are therefore exactly the differences \(b-a\) with \(b\in B\), \(0\le a<b\) and \(a\notin B\), with multiplicity. For each bead \(b_i\) the product of its hole differences is \(b_i!/\prod_{j>i}(b_i-b_j)\), so the hook product is \(\prod_i b_i!/\Delta(b)\). Together with the identity character formula this gives the classical hook-length degree formula and shows why equal hook multisets give equal degrees at a common size.

Use \(A^*(z)=A(z^{-1})\) and the same convention for \(W\). The identity
\[
\frac{AA^*-1}{(z-1)(z^{-1}-1)}
=-W\frac{z}{z-1}+\frac{W^*}{z-1}+WW^*
\]
is interpreted as a Laurent expansion at infinity. At degree \(h>0\) its terms contribute minus the number of beads \(\ge h\), zero, and the number of bead pairs differing by \(h\), respectively. The sum is minus the number of hooks of length \(h\). Hence equality of \(AA^*\) implies equal hook multisets.

The size of the partition equals
\[
\nu(A)=\tfrac12\big(A''(1)+A'(1)-A'(1)^2\big).
\]
Indeed \(A'(1)=|B|\) and \(A''(1)=2\sum_{b\in B} b\). Subtracting the staircase gives the formula. For any \(A,P\) taking the value 1 at 1, the product rule gives \(\nu(AP)=\nu(A)+\nu(P)\), because the mixed derivative term cancels. If two boundaries agree modulo \((z-1)^{r+1}\), their occupancy polynomials agree modulo \((z-1)^r\). Their derivatives through order \(r-1\) agree, giving equal falling-factorial sums through that order. The triangular change to ordinary powers gives equal cardinalities and power sums through \(r-1\).

## A reversal pair and independent choices

Use the even \(r\) fixed above. By binary uniqueness the Thue–Morse polynomial
\[
Q(z)=\prod_{j=0}^{r-1}(1-z^{2^j})=\sum_{u=0}^{L-1}\epsilon_u z^u
\]
has coefficients \(\epsilon_u=(-1)^{s_2(u)}\), where \(s_2(u)\) counts the one-bits. Complementing all \(r\) bits preserves their parity, so \(\epsilon_{L-1-u}=\epsilon_u\). In positions \(0,\ldots,E-1\), set occupancy \(w_0=0,\ w_{E-1}=1,\ w_{u+1}=(1+\epsilon_u)/2\). Define \(F=1+(z-1)\sum_i w_i z^i\) and \(R=z^E F^*\). The occupancy of \(R\) at \(i\) is \(1-w_{E-1-i}\), by the geometric sum for \((z^E-1)/(z-1)\). It is zero at 0 and one at \(E-1\), so \(R\) is also a boundary of degree \(E\). The endpoints cancel in the occupancy difference, and at interior positions the difference is \(\epsilon_u\). Hence
\[
F-R=z(z-1)Q(z),\qquad FF^*=RR^*.
\]
Every factor of \(Q\) has a simple zero at 1. This gives distinct valid boundaries with equal reciprocal products and agreement modulo \((z-1)^{r+1}\).

For each of the \(2^k\) choices of \(F_j\in\{F,R\}\) take \(C(z)=\prod_{j=0}^{k-1}F_j(z^{M^j})\). Before factor \(j\), the degree is \(M^j-1\). At that step the translates of the earlier polynomial by the occupied exponents of the new factor are disjoint. In each translate the first and last coefficients have the sign of the translating term. As those signs alternate, the result is again a boundary. The coefficient at \(uM^j\) for \(0\le u\le E\) recovers the coefficient of \(z^u\) in \(F_j\) by radix uniqueness and the constant terms 1. All choices are distinct. Each has degree \(D\), and all have the same reciprocal product. Substituting \(z^{M^j}\) preserves divisibility by \((z-1)^{r+1}\), and products preserve congruence, so all choices have the same jet. As \(r\ge2\), they have a common partition size \(n_0\). All occupied positions are less than \(D\), so \(n_0\le\sum_{t\in B}t\le D^2\).

## Padding at every size

A partition with \(u\) rows of length \(a\) and \(v\) rows of length \(b\) has occupied intervals \([a,a+u-1]\) and \([b+u,b+u+v-1]\). Its boundary is
\[
P(z)=1-z^a+z^{a+u}-z^{b+u}+z^{b+u+v}.
\]
For \(u,v\ge a=D+1\), its consecutive gaps \(a,u,b-a,v\) exceed \(D\). Thus multiplication by \(P\) gives separated signed translates of each \(C\), preserving the boundary property. Since all nonconstant terms in \(P\) have degree greater than \(D\), the coefficients through \(D\) preserve distinctness. A common \(P\) also preserves the reciprocal products and jets. The size becomes \(n_0+au+bv\).

For any \(n\ge U(d,k)\), put \(T=n-n_0-(a+b)a\); then \(T\ge Db\). With \(b\equiv1\pmod a\), let \(v'\) be the least nonnegative residue of \(T\) modulo \(a\). It satisfies \(v'\le D\), so \(u'=(T-bv')/a\) is a nonnegative integer. Take \(u=a+u'\), \(v=a+v'\). Then \(n=n_0+au+bv\). The padded partitions therefore have size \(n\), equal hook multisets, and equal beta cardinalities and moments through \(d\) since \(r-1\ge d\). Their corresponding irreducible complex characters agree on every support-\(\le d\) permutation. Distinct partitions index inequivalent irreducibles, whose characters are distinct by character orthogonality. Choose any \(k\) of the \(2^k\) witnesses.

For the finite test statement, extension acts as the original permutation on its embedded letters and fixes the complement. It preserves nontrivial cycles. In \(S_n\) the multiset of nontrivial lengths determines the number of one-cycles by subtracting its sum from \(n\). A permutation with the extended full type has the same support size as the test, at most its arity and hence at most \(d\). This completes the finite test implication.

## Sources and formal companion

Craven's Conjecture 3.5 appears on p. 9 of arXiv:2410.01726v1 and p. 11 of v3. The earlier uniform hook-cluster result is Craven, *Symmetric Group Character Degrees and Hook Numbers*, arXiv:0709.0897v1, Theorem 1.4. Its bead–hole description and Xiong, arXiv:1501.01522v1, Lemma 2.1 and Theorem 1.2, give context for reflection and hook equivalence. The character reduction uses the classical Frobenius formula and agrees with the bounded-degree mechanism in Okounkov–Olshanski, *Shifted Schur Functions*, §15. The construction above couples equal reciprocal products to high-order beta-moment agreement, then preserves both through radix amplification and padding at every large size. The proof uses no numerical experiments.

The [Lean appendix](LEAN-SOURCE-APPENDIX.md) contains the 58 byte-exact canonical modules. The [crosswalk](SOURCE-CROSSWALK.json) gives the native and formal anchors. The ordinary proof invokes classical character theory and symmetric polynomial identities. The Lean proof constructs actual irreducible traces through signed coloring characters, their norm-one realization and positivity at the identity, and implements the bounded moment step using its own polynomial coefficient development. In the Lean proof the positivity used to select the sign is established internally. The manuscript assembles previously reviewed hand arguments, with the bound aligned to the formal construction. This assembly check is separate from later independent review of the manuscript. Source provenance and the limits of source and prior-art coverage are recorded in the replay report.

