# Second-pass mathematical depth, 2026-11-01

Zero proposed credit. These are exact-target investigations, not forty new record reviews. All forty old statements and reasons were read from the hash-bound r390 disposition file before choosing these routes. Its SOURCE-READING.md, SUMMARY.md, FAILURES.md and historical-matches.json were read as well. The old source failures and qualification objections remain part of the evidence. All paths below are within this packet unless explicitly identified as read-only ancestors.

## 383944: four linear equations versus codimension three

**New primary restoration.** AIM original HTTP section1, exact anchor 6ece8953664f1897b245a9221309e430, includes the status: “Numerical results suggest that there are 4 constraints but they only intersect the trifocal tensor variety in codimension three.” Thus answering only four linear constraints would omit the mathematical point. The MathDB literal is unchanged in inherited.json/raw. This pass used the original HTTP source specified in the record, without certificate bypass, cookies, alternate routing or retrying the old HTTPS failure. HTTP transport is not authenticated; this limits source assurance.

**Actual bodies read.** Tsakiris–Vidal JMLR19(2018), pp38–40, equations145–151 and derivation, plus the paragraph distinguishing ambient rank4 and geometric codimension3. Kileel1611.05947v1 Proposition13 and its whole short proof; Theorem21 statement and whole computational proof. The latter is specifically CALIBRATED and uses probability-one numerical decomposition for the variety-intersection assertion. It is not an exact symbolic proof of every uncalibrated component, and was not promoted to such. The request for v2 returned404; v1 was then obtained normally. No publisher-body equivalence or complete dependency audit is claimed.

**Independent ordinary calculation, ambient stage.** Over a field, take three nonzero projective point representatives. Independent basis changes send each to e1 and give invertible changes of tensor coordinates. Contraction by the first point surjects onto 3x3 matrices; multiplying by the two cross-product matrices selects, up to signs/transposition, the bottom-right 2x2 block. Its four entries are independent coordinates. Hence exactly four independent ambient linear equations. This applies to all nonzero representatives, not an integer sample.

**Second stage, why this does not give codimension four.** Normalize the first camera to [I|0]. Write the other cameras [B|b] and [C|c]. Up to the harmless slice convention/transposition, T1=B1 c^t-b C1^t. With point triple e1,e1,e1, let u,v be the bottom two entries of B1,C1 and b,c denote the corresponding last-column tails. Constraints are Fij=u_i c_j-b_i v_j=0. On the nonempty chart b0*c0 !=0, the first three equations solve exactly

    lambda=u0/b0, v0=lambda*c0, u1=lambda*b1, v1=lambda*c1.

The remaining equation follows. Conversely these assignments solve all four equations. Algebraically,

    b0*c0*F11 = b1*c0*F01 + b0*c1*F10 - b1*c1*F00.

Thus this chart is a graph in three eliminated coordinates, and has codimension3 in the camera-parameter chart. The diagnostic checks ambient rank4 and Jacobian rank3 at a valid rational point, but those checks alone do not prove genericity. The graph description supplies the ordinary chart argument.

**Third stage / objection.** Transferring this to the full projective trifocal image requires camera-rank opens, orbit-fibre control, and excluding extra components larger than this chart. A single Jacobian sample cannot certify that. Kileel already studies the same discrepancy and JMLR explicitly gives the rank/codimension conclusion for the uncalibrated setup; no new significant mechanism has been found. We do not claim Kileel's calibrated numerical component count is an exact full-scope uncalibrated symbolic certificate. Outcome: no novelty-qualified candidate, retain precise image/degenerate-component gap rather than manufacture a four-equation Lean endpoint. Formalizing just the rank would be a helper, not an eligible solution.

## 383930: boundary perturbation preserving F-purity and changing index

**Source restored.** AIM minimalmodcharp/3 exact anchor9f1dec7ec10ffe36e3b0f46d0d01e269 agrees with the literal pair question; title “Construction of F-pure centers” does NOT impose an extra requirement to construct a specified center. It supplies no global/affine restriction. Do not assume strong F-regularity means global F-regularity on a projective scheme.

**Actual bodies read.** Hacon–Xu1302.0298v1 Definition2.6, Theorem2.7 (proof is a citation), complete Lemmas2.8,2.9,2.13 proofs. Schwede–Smith0905.0404v2 Theorem4.3 and complete proof; Lemma4.9 statement and first composition argument, Corollary6.9/proof and Question7.2. Ajit2610.38163v1 Theorems1.1,1.4 and Corollaries1.2–1.5; complete Lemma5.8 and Theorem1.4 proof. The affine interpolation proof, Proposition5.3, Theorem5.4 and Proposition5.7 were NOT fully audited. Its abstract alone was only a lead. This is a new preprint posted28October2026, with manuscript date30October; no published-version body is claimed.

**First mechanism, explicit index arithmetic.** Assuming K+Delta is Q-Cartier, choose m prime to p and e0 with m*p^e0*(K+Delta) Cartier. Choose effective E with E-K Cartier. Let H=Supp(E+Delta) and

    D_e=(Delta+E)/(p^e-1), e>=e0.

Then m(p^e-1)(K+Delta+D_e)=m*p^e*(K+Delta)+m*(E-K) is Cartier. Its displayed multiplier is prime to p. D_e>=0 and tends coefficientwise to0 on fixed H. This is exactly the old Hacon–Xu perturbation, not a discovery. D=0 would still miss the index condition and remains rejected.

**Second mechanism, uniform purity margin.** On an affine strongly F-regular pair, a splitting for a fixed effective Cartier divisor dominating H gives a positive rational margin epsilon for which Delta+epsilon H remains F-pure. Choose e large enough D_e<=epsilon H and use monotonicity of splitting under decreasing boundary. With a finite affine cover, take the minimum positive margin to preserve local purity everywhere, provided the same GLOBAL effective E and domination divisor exist. This is stronger than just checking an arithmetic index. It needs hypotheses for global E and Q-Cartier canonical boundary, and quasi-compactness. The Hacon–Xu lemma plus that margin is a routine bridge in the qualified quasi-projective setting, not new credit.

**Third mechanism, global maps / recent prior art.** Schwede–Smith use a dualized splitting to obtain Delta1 with K+B+Delta1 Q-trivial and Delta2 with K+B+Delta2 anti-ample, then mix boundaries using splitting composition and a margin to retain F-regularity; Remark4.10 supplies prime-to-p index. This applies to globally F-regular pairs and affine cases. It cannot silently be applied to an arbitrary locally strongly F-regular projective pair. Ajit's global theorem passes from a normal section ring and homogeneous map to a boundary on Proj. Its displayed theorem is for the unprescribed boundary problem (B=0), not automatically for the present prescribed Delta. The fixed-Delta Cartier-subalgebra/homogeneous globalization extension has not been proved here.

**Precise remaining gap.** Restore the intended global class of X and boundary convention, or prove existence of the single effective E/domination divisor in that exact class; if K+Delta is not assumed Q-Cartier, supply a global fixed-Delta map-to-divisor construction. No assertion that a public theorem fully resolves all literal schemes, and no novelty clearance for an extension. Known affine and quasi-projective perturbation cases do not justify investing in a surrogate Lean predicate. Park source/globalization gap, with substantial classical-overlap warning.

## 384169: nested full twists and parity

**Source restored.** AIM catheckehilbert/2 literal positive products FT_k, k<=n, parity plus recursive formula. 384167 and384168 source problems on that page were also read; they receive statement-context depth only, not full proof review. In particular, nested-full-twist braids must not be conflated with every algebraic braid.

**Actual proof read.** Turner2410.03068v1 Definitions1.1,2.1,2.3; Conjecture1.2; Theorem1.5 proof; equations2–4 and their local-parity precondition; complete Lemmas2.4–2.7 proofs, Corollary2.8; complete Lemmas2.9–2.10 proofs; Corollary2.15 and Theorem2.16 proofs. Lemmas2.11–2.13 were inspected only through their use and displayed context, not fully independently audited. Figure1 schematic homotopies and cited Soergel foundations were not reconstructed. Published correspondence and all later citing bodies remain unchecked.

**Mechanism A, normalize exact scope.** A positive product has exponents a2,...,an>=0. Set d1=a_n,d2=a_n+a_(n-1),...,d_(n-1)=sum a_k and d_n=d_(n-1). Then Turner's beta(d1,...,dn)=FT_n^a_n ... FT_2^a2, since the nested twists commute. Conversely the differences in a nondecreasing d recover the exponents. Therefore the all-n conjecture exactly contains the reserved family; n=4 is not the full solution. Duplicate exponents, n=3 or pure full twists are parameter cases.

**Mechanism B, try the local K recursion.** K_r JM_(r+1) splits into shifted K_(r+1) and K_r terms. If BOTH are already parity, the connecting differential vanishes by homological parity and Hilbert series add. For n=4 the auxiliary states A(n,m,l)=K1 FT2^l FT3^m FT4^n, B(n,m)=K2 FT3^m FT4^n, C(n)=K3 FT4^n reduce positive exponents by equations2–4. This is not a parity proof until the zero-exponent faces close.

**Mechanism C, follow the zero face rather than assuming it.** B(n,0) produces K2 JM4 FT4^(n-1); commuting/conjugating creates sigma3^(2k)B(n-1,0). Turner closes this state using sigma3^(2k)C(n), then reaches two-strand full twists. The next twisted state sigma2^2 sigma3^(2k-2)B(n,0) produces a terminal-strand JM_3 variant (Lemma2.9); Lemma2.10 closes that with explicit three-strand conjugation and absorption. These extra states explain why applying local recursion alone was circular. For n=5 the corresponding zero face K2 JM5 ... creates multiple interacting tail crossings, with no proved finite parity-closed normal form here. Positivity of a decategorified polynomial does not force the connecting maps to vanish.

**Remaining lemmas for an actual full-scope endpoint.** A well-founded family of auxiliary Soergel complexes for arbitrary strand number, closure under the cone recursion AND zero faces, proof of parity for every terminal object, and a grading-preserving identification with literal HHH including all three grading conventions. No such general closure argument was found. A finite sweep of braid words or n<=4 would not close it. Park this honest categorical gap. No n=4 rediscovery, no all-n exclusion, no Lean theorem asserted.
