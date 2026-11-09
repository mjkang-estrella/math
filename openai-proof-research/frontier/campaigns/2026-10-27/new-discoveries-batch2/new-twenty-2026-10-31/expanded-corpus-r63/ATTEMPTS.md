# Sustained routes

## 367804: exact star-count reversal, then prior-art exclusion

Primary Corollary 8, Theorem 9 and Conjecture 10 were read with the construction G_n^ell(i)=K_(i+ell)+(I_i union K_(n-2i-ell)). For t>=2 the count is (i+ell) C(n-1,t)+i C(i+ell,t)+(n-2i-ell) C(n-i-1,t). The t=1 count is half the degree sum.

An initial exact sweep was followed by symbolic analysis, not treated as proof. For fixed ell=2, n=2m, i0=m-2, t=m+1, m>=5, the two counts are m C(2m-1,m+1)+2 and 3 C(2m-1,m+1)+(2m-4) C(2m-2,m+1). Their difference is (m-5)/(2m-1) C(2m-1,m+1)+2>0. Since 2t=2m+2<2m+3=n+ell+1, this reverses the asserted inequality for arbitrarily large n with fixed ell. This survives the asymptotic quantifier; finite small-n failures alone would not.

Live search located Liu–Yang–Zhang, arXiv:2607.00770v3 (July 2026). Its actual Section 2 critical-case proof, not merely its abstract, computes the same-parity difference f=g(1)-g(i0) as [n-ell(n-3-ell)]/[2(n-1)] C(n-1,(n+ell)/2)-2. Substitution ell=2,n=2m gives the negative of the formula above. This is a complete explicit subsumption bridge. EXCLUDE as already refuted; no Lean investment or new-credit proposal. The neighboring threshold Theorem 8 is not claimed as our result.

## 367881: exact five-vertex spectral violation; HOLD

The primary definitions Q=D+A, ordered eigenvalues, c=e-n+1 and Conjecture 1 were read. The graph in Figure 1 has one universal hub, a second hub adjacent to it and the c shared triangle vertices, and s pendant vertices at the universal hub. The figure's embedded SVG provides the edge data; graphical interpretation still needs independent fidelity review.

For n=5,c=2, the claimed graph B has edges 01,02,03,04,12,13. The connected friendship graph F has edges 01,02,03,04,14,23. Both have 5 vertices and 6 edges, hence c=2 in the source range. Their Q characteristic polynomials are
B: (X-2)(X-1)(X^3-9X^2+20X-8),
F: (X-3)(X-1)^2(X^2-7X+8).

For p=X^3-9X^2+20X-8, p(1/2)=-1/8, p(1)=4, p(2)=4, p(3)=-2, p(5)=-8, p(6)=4. IVT and degree 3 give exactly three roots r in (1/2,1), a in (2,3), b in (5,6). Therefore S2(B)=a+b=9-r<17/2. For F the eigenvalues are (7+sqrt17)/2,3,(7-sqrt17)/2,1,1, so S2(F)=(13+sqrt17)/2>17/2. This proves an ordinary fixed-c violation, not just a numerical tie. No claim that F is globally maximal is needed.

A labeled exhaustive diagnostic through n=6 and a seeded n=7 sample were followed by this exact characteristic-polynomial and root-isolation mechanism. The numerical values only suggested the proof. A literal Lean graph-to-spectrum endpoint was not completed. Source's 2026 publisher version was not obtained; the failed publisher URL was an unverified guessed PII and is NOT evidence about the actual published article. No denial retries were made. Root should assess the significance of a small-order exception; do not count this as a qualified discovery. Remaining formal obligations: finite graph construction and c, charpoly identities in Lean, ordered real-root/eigenvalue multiplicities, and final extremal-negation assembly. No surrogate certificate supplied.

## 368007: homogeneity, signed equilibria, exact full local-minimum proof

A dilation argument alone yields only E=0 at a stationary configuration, since the energy is homogeneous of degree -(n+2s). That does not exclude flat local minima. Considering three charges rather than a zero mass exposed the missing mechanism: opposite-sign middle mass balances the attraction of two outer equal masses. In one dimension at exponent 2, the ratio is -1/8, and the exact gap factorization is nonnegative on an open chamber. This route is carried through to the full Lean endpoint; see PROOF.md. No small numerical sweep is used to establish it.

## Other source pitfalls retained

368710 is already proved by the very source cited by MathDB: Theorem 3 and its proof use Lemmas 1–5 to force a clique of support vertices, then a one-to-one leaf attachment. No discovery claim.
368022 remains open in its source despite the MathDB sentence saying solved: the source proves a converse characterization and reports computational verification through k=7. No credit for correcting metadata.
368535 is refuted in its cited source. The signed construction and forest-to-balanced-set bridge are source material, not a new counterexample.
368220 source Remark 4.14 retracts an earlier claimed computational counterexample because of inconsistent node labels. Do not recycle that witness.
