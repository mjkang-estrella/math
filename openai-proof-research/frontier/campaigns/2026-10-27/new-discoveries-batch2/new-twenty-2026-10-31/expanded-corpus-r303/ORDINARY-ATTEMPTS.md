# Sustained ordinary attempts — no qualified endpoint

All arguments here are symbolic ordinary reasoning. No mathematical enumeration, solver, numerical search, Lean execution or children were used. A partial identity or special case earns zero credit.

## 357152: prescribed cubes

The exact endpoint is existence of translations of every prescribed J_i-subcube with union cardinality at least d+q, d=sum |J_i|<2^(n-1). Source Conjecture 5.2 and its singleton matching Theorem 5.3 were read in v1, v2 and current v3.

Route A: let M=2^n and U be the union so far. For a uniformly translated s-dimensional cube, the expected intersection with U is 2^s |U|/M. If |U|<M/2, some translation intersects U in at most 2^(s-1)-1 points. It therefore contributes at least 2^(s-1)+1 ≥ s+1 points (s≥1). This gives a genuine inductive mechanism until the half-full barrier. It does NOT solve the conjecture: the required d+q can be arbitrarily close to M, and after passing M/2 the next increment bound fails. Ordering large cubes last may exploit their surplus, but no inequality disposing of every possible remaining singleton multiset was obtained.

Route B: expand each J_i into its list of directions and apply the source prescribed-direction matching theorem to the total d directions. The matching has 2d distinct endpoints. To infer the desired d+q union, one needs to regroup the |J_i| matching edges into a translate of a single J_i-cube for each i without losing too many distinct endpoints. Independent matched edges can have different fixed coordinates outside J_i; the matching theorem does not make them cofacial. Closing the group by taking an affine subcube can change its direction set and violate the literal requirement. Missing lemma: a prescribed grouping-compatible packing, not merely a matching.

Route C: independent random translates yield expected union M(1-product_i(1-2^|J_i|/M)). A sufficient Bonferroni estimate is sum_i 2^|J_i| − sum_{i<j}2^(|J_i|+|J_j|)/M ≥ d+q. This fails to prove the all-singleton case, because its first term already equals d+q and every overlap term is a loss. Thus it cannot replace the exact matching input. A successful mixed proof must marry its higher-dimensional surplus to matching flexibility. No such coupling is proved. No finite object is claimed as a counterexample.

## 364822: partition multiplicities and finite differences

Read source definitions: m_j counts occurrences of part j, not the jth power moment. ImP_k(n) is the SET of images of partitions of n of length at least k. Across different n the source uses disjoint union. Delta is forward difference in n. The latest journal URL returned an Incapsula challenge (212 bytes, status200), so it is inaccessible; no retry or substitute for that denied source was made. v1,v2,v3 Conjecture18 passages agree. Printed tables/figures and full journal proof are not cleared.

Route A: work first with counts over input partitions (a proxy, explicitly not the endpoint). Put P(q)=product_{j≥1}(1−q^j)^(-1). A selected k-subset of parts with product p prime must consist of one p and k−1 ones. The rooted preimage count has generating function
P(q) q^(p+k−1) / ((1−q)^(k−1)(1−q^p)).
The first k−1 coefficients vanish, so applying k−1 forward differences multiplies by ((1−q)/q)^(k−1), giving P(q)q^p/(1−q^p), the generating function for m_p(P(n)). This proves the desired prime identity for preimage-weighted counts. It does NOT prove it for distinct image sets.

Route B: analyze collision fibers rather than silently assuming global injectivity. If an input has a≥k ones, its image contains binomial(a,k) ones, which determines a uniquely. For each j>1 the contribution involving a single part j and k−1 ones is binomial(a,k−1)m_j; every other product equal to j uses only parts smaller than j. Inductively this recovers all multiplicities m_j. Thus pre_k is injective on the positive-one-output fibers. Any input with the same image also has a≥k, so this reconstruction suffices for those fibers. It establishes the p=1 identity by the generating function P(q)q^k/(1−q)^k and forward differences, but only one conjunct of the full record. This is a classical rooted-count/reconstruction bridge, credit0.

For prime p and composites in the other identities, contributing inputs may have only k−1 or k−2 ones, so binomial(a,k)=0 and the reconstruction starting value is unavailable. Merely knowing the weight n does not yet replace it. Missing lemma: pre_k fiber injectivity (or an exact aggregate collision correction) on all contributing input families, uniformly k and n.

Route C: composite4 has selected-part types (4,1^(k−1)) and (2,2,1^(k−2)). Rooted preimage series is
P(q)[q^(k+3)/((1−q)^(k−1)(1−q^4)) + q^(k+2)/((1−q)^(k−2)(1−q^2)^2)].
After k−1 differences this becomes
P(q)[q^4/(1−q^4) + q^3(1−q)/(1−q^2)^2].
The adjacent-n sum multiplies the transformed series by 1+q^(-1); elementary simplification gives
P(q)[(1+q^(-1))q^4/(1−q^4)+q^2/(1−q^2)],
exactly the first conjectured right side for rooted preimages. Boundary terms vanish because selected parts have total input weight at least k+2. This is a second substantive reduction but retains the SAME image-fiber gap. Product6 adds the selected types (6,ones) and (2,3,ones), and product9 adds (9,ones),(3,3,ones); factoring these is not a substitute for that bridge. Related 2026 papers addressing Conjecture19 or global injectivity are leads, not proof-body clearance of this exact endpoint. No dormant execution task is justified.

## 363750: zero Krein parameters versus a whole cyclic module

Source Sections8–9 give the actual six operators, their self-adjointness, and Lambda=T(1 tensor1 tensor1), irreducible. The tensor-factor E operators are ordinary Bose–Mesner projections; the starred operators are distance-dependent diagonal maps on pairs of tensor coordinates. They cannot be interchanged on the strength of notation.

Route A: let v0=sum_x x tensor x tensor x. It belongs to Lambda. For P=E_h tensor E_i tensor E_j the source defines Q_hij=|X|P v0 and proves ||Q_hij||²=|X|m_h q^h_ij. As |X|m_h>0, if q is nonzero then P v0 is nonzero and P Lambda is nonzero. Consequently P Lambda=0 implies q=0. This direction is already an immediate public source deduction.

Route B: q=0 implies P v0=0. Because Lambda is irreducible and v0≠0, v0 also generates Lambda. It is tempting to conclude P Lambda=0. That inference is false for a general operator on a cyclic irreducible module. One must prove P A_w v0=0 for EVERY word A_w in the six generators, or prove ker P contains an invariant submodule containing v0. The three unstarred generators commute with P. The starred ones need not. Source Section8 only controls which neighboring spectral indices a single starred generator can reach; neighboring nonzero sectors can feed a zero-Krein sector. No simultaneous-zero closure identity was established.

Route C: translation schemes offer Fourier characters. The regular translation action forces invariant tensors to have product of characters trivial, while q^h_ij counts compatible character triples across the three dual classes. If q=0 there are none, so the corresponding projection annihilates the invariant tensor space, hence Lambda. This is a special class using abelian regular symmetry, precisely the source Problem12.4 direction. The companion scaffold duality paper was retrieved and selected theorem/definition passages inspected, not fully audited. General distance-regular graphs need not have such symmetry. Replacing Lambda by all automorphism-invariants does not create the missing character decomposition. Hamming/translation cases receive zero new credit and do not settle the literal all-graphs assertion.

The latest accessible journal body retains Conjecture12.2. This is evidence about that body only, not a current global open-status certification. All primary versions listed for this source consist of v1; companion/citing-body coverage is bounded and incomplete. No complete full-scope endpoint, candidate file or Pi plan is promoted.
