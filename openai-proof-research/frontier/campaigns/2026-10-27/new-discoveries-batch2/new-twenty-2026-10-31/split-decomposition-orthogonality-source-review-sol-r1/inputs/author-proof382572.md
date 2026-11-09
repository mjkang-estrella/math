## 382572: full source-dependent ordinary implication
The actual original math/0608694v1 Definitions10.1–10.2 define the spaces by two spectral flags and orthogonal complements; Assumption8.1 requires a distance-regular graph with classical parameters (D,b,b-1,beta), b not1. The primitive-idempotent ordering is the formally self-dual Q-polynomial ordering fixed in Remark8.2. Work over the standard Hermitian complex vector space. Section7 explicitly gives an orthogonal decomposition V into irreducible T-modules, because T is closed under conjugate transpose. No arbitrary-pair-of-flags assertion is used.

Fix such a decomposition V=orthogonal direct sum W. In a summand write rho,tau,d for its endpoint, dual endpoint and diameter. Lemma11.3 gives four decompositions of W: the eigenspaces of x02,x13,x12,x30, each indexed h=0,...,d. Lemma11.4 places these respectively in the global split spaces with indices
DD: (rho+d-h,tau+h),
UU: (D-rho-h,D-d-tau+h),
DU: (rho+d-h,D-d-tau+h),
UD: (D-d-rho+h,tau+d-h).
(The source's order x12,x30,x02,x13 has merely been reordered.) Every decomposition is a direct sum, by semisimplicity in Lemma11.3; each spans W. Their sums of indices are respectively
cDD=rho+tau+d,
cUU=2D-rho-tau-d,
cDU=D+rho-tau,
cUD=D-rho+tau.

Here is the required global equality bridge, rather than just an inclusion claim. For any one orientation, collect all its W-pieces by their global (i,j). They lie in the corresponding tilde space. They span V since each W is spanned. Lemma10.3 says the global tilde spaces form a direct sum. For v in one tilde space, decompose v into W-pieces and group by index; uniqueness in the global direct sum forces every other index-group to vanish. Thus the tilde space is exactly the sum of the collected W-pieces with that index. In particular its projection onto W vanishes off the relevant index-sum c.

Take u in DD(i,j), v in UU(r,s). The Hermitian inner product is the sum over W of their W-projections. In any W in which both projections survive,
i+j=cDD, r+s=cUU, hence (i+r)+(j+s)=2D.
If (i+r,j+s) differs from (D,D), one coordinate is less than D. If i+r<D, u lies in sum E*_0,...,E*_i and v lies in sum E*_{D-r},...,E*_D. These supports are disjoint orthogonal eigenspaces, so the pairing is zero. If j+s<D the same argument uses E_0,...,E_j and E_{D-s},...,E_D. The source's real symmetric primitive idempotents give these orthogonal decompositions. Cross-module terms vanish by orthogonality of the fixed W-decomposition. This proves the first asserted orthogonality for ALL indices, including zero split spaces.

For DU(i,j) and UD(r,s), surviving W-projections have index sums cDU+cUD=2D again. The E* flags have the same directions as in the first argument. The E flags are reversed: if j+s<D, the high E-support E_{D-j},...,E_D of DU and low support E_0,...,E_s of UD are disjoint. The other case uses E*. This proves the second assertion.

No thinness, equality rho=tau, uniform dimension of modules, additional graph classification, or choice of q real is required. All index inequalities come from Lemma7.1 and Lemma11.4. Diameter restrictions in the source standing setup are retained; this is not a theorem about undefined decompositions outside that setup.

Two independently checked routes beyond the failed universal-flags shortcut: (1) the support-sum argument above; (2) for fixed W, pairing DD index h against UU index k is zero on one flag when h+k<d and on the other when h+k>d (substitution into the displayed index table), leaving only h+k=d, which is exactly both complementary indices. DU versus UD leaves h=k after the analogous substitution. The global equality bridge is needed in both routes and is explicitly supplied.

Actual 2005 companion math/0306142 Lemma6.1 proof was read: project a lower intersection vector to W using the orthogonal T-module decomposition. Its projection lies in an intersection of adjacent split summands W_h and W_{h-1}, which is zero by their directness. This proves orthogonality to both lower intersections. The 2006 Lemma11.4 explicitly gives the three reversed-order variants and cites this argument. The derivation uses actual primary statements and proof text; its deeper tridiagonal-module input remains attributed, not independently re-proved here.

Significance assessment: the strongest contrary case is that the source itself explicitly prints this exact claim as Conjecture13.6, despite its Lemmas11.3–11.4. Thus an open label must not be replaced by a shortness judgment. Nevertheless the complete source-result-to-target bridge above imports the source's four decompositions verbatim and adds only direct-sum uniqueness and orthogonal spectral supports. This is a concrete routine-adaptation exclusion proposal, not an authenticated claim that the exact corollary was printed previously. A separately identified Kim2009 paper on these matrices is relevant but its body was NOT acquired/read and no theorem is falsely attributed to it. Independent fidelity/significance/body audit and current registry clearance have not happened. Zero qualified credit, no formal dispatch.

