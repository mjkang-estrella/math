# Crossing-number contribution review, round 1

2026-10-16. Independent primary-literature contribution review of the frozen candidate for the ordinary crossing number of \(K_n\) minus one edge, and for the Cartesian product of a complete graph with a path. This file does not accept the proof, does not increment the campaign count, and does not certify worldwide priority. The proof gate in `kn-minus-edge-proof-r1` is a separate assignment. Nothing there is treated as passed.

## Verdict

**SUBSTANTIAL**, conditional on that proof gate, for one package.

The package is the full statement in the frozen candidate: for every \(n\ge 2\) and every edge \(e\),

\[
\operatorname{cr}(K_n-e)=\frac14\Big\lfloor\frac{n+2}{2}\Big\rfloor\Big\lfloor\frac{n-1}{2}\Big\rfloor\Big\lfloor\frac{n-3}{2}\Big\rfloor\Big\lfloor\frac{n-4}{2}\Big\rfloor,
\]

together with the one application, for \(m\ge 4\) and \(n\ge 1\), of the Ouyang–Wang–Huang product identity to the same formula. In the Ouyang–Wang–Huang convention, \(P_n\) has \(n\) edges.

The substantial content is the odd lower bound for \(n=2s+1\ge 15\). The even case, the odd cases \(n\le 13\), the matching upper bound, and the product identity are classical once the pinned Harary–Hill theorem is granted. They belong in the same paper because they are the remaining pieces of one formula and one formal substitution. They are not a second finding. The first product order that uses the new lower bound is odd \(m\ge 13\). The product at odd order \(11\) uses only \(\operatorname{cr}(K_{13}-e)\), which integrality already closes.

A correct proof of that odd lower bound is a genuine bridge across the pinned odd argument for \(K_n\). It is not a substitution of constants into that argument, and it is not the repair used for \(K_{m,n}-e\) in the Sadhu preprint read below. If the proof gate finds a gap in the localization, the degree budget, or the descent, this verdict does not fill the gap.

## Statement under review

Primary text: `frontier/campaigns/2026-10-14/fresh-substantial-discovery-r2/candidate.md`, 23029 bytes, SHA-256 `2a078a07142986c93845f4855496db14e41ee2590adc17720727b19145dd1c8b`. Read in full, with the README, source contracts, provenance, manifests, and both check scripts.

Pinned OpenAI mathematics at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated. The complete-graph manuscript used below was read in the local copy whose hash matches the candidate's contract. Its Harary–Hill theorem is an input. It is not part of the new contribution.

The ordinary crossing number counts every interior crossing of a drawing by continuous arcs. The candidate fixes one missing pair \(\{a,b\}\) and invokes edge-transitivity of \(K_n\).

## What already gives the formula outside the odd range \(n\ge 15\)

These parts are included so the paper can state every \(n\). Each one was checked against the primary text named here.

**Upper bound, every \(n\ge 4\).** Delete one edge from a drawing of \(K_n\) that already has \(Z(n)\) crossings and at least \(\binom{\lfloor(n-1)/2\rfloor}{2}\) crossings on that edge. Chia and Lee, Lemma 1, construct that drawing on a cylinder and obtain \(\operatorname{cr}(K_n-e)\le Z^*(n)\) for \(n\ge 5\), where \(Z^*(n)=Z(n)-\binom{\lfloor(n-1)/2\rfloor}{2}\). Ouyang–Wang–Huang, Lemma 2.3, record the same closed form and attribute it to Zheng, Lin, Yang, and Cui. The candidate's Section 5 counts the same quantity in the pinned endpoint-sum two-page drawing. That count matches the classical upper bound. It is a verification inside a drawing the pinned manuscript already analyzes.

**Even \(n=2M\ge 6\).** Ouyang–Wang–Huang, Theorem 3.2, prove
\[
\operatorname{cr}(K_m-e)\ge\frac{m+2}{m-2}\operatorname{cr}(K_{m-1})
\]
for \(m\ge 3\), by restoring the missing edge along each path of length 2 through a third vertex and comparing vertex responsibilities. Theorem 3.3 says that if \(\operatorname{cr}(K_{2M-1})=Z(2M-1)\), then \(\operatorname{cr}(K_{2M}-e)=\frac14(M^2-1)(M-2)^2\). The pinned theorem supplies the hypothesis for every \(M\). The identity \(\frac{2M+2}{2M-2}Z(2M-1)=\operatorname{target}(2M)\) was rechecked in `gap-check.py` for \(6\le 2M\le 38\). Chia and Lee, Theorem 2, is the same even conclusion, under the same odd complete-graph hypothesis, with a responsibility argument of the same shape. Their Remark 2 states that this exact formula is the even-order case. Either citation, plus the pin, closes every even order. The candidate's Section 4 rewrites the Ouyang–Wang–Huang calculation and observes that the local crossing numbers \(m_i\) cancel, so the geometric bound \(m_i\le\lfloor(n-3)/2\rfloor\) is not required for the even case. That observation stays inside Theorem 3.2.

**Odd \(n\le 13\).** Ouyang–Wang–Huang, Theorem 3.1, is
\[
\operatorname{cr}(K_m-e)\ge\frac1m\Big(2\operatorname{cr}(K_{m-1})+(m-2)\big(\operatorname{cr}(K_m)-\lfloor(m-3)/2\rfloor\big)\Big).
\]
Chia and Lee, Theorem 1, is the same expression, written with the two complete-graph hypotheses \(\operatorname{cr}(K_n)=Z(n)\) and \(\operatorname{cr}(K_{n-1})=Z(n-1)\). After the pin, the bound is an explicit rational. For odd \(n=2s+1\le 13\) its ceiling equals the integer target. For \(n=13\) the bound is \(2720/13\) and the ceiling is \(210\), the target. Ouyang–Wang–Huang, Theorem 3.4, and Chia and Lee, Corollary 1, already published the equality through \(n=12\), using Harary–Hill through \(n=12\). The case \(n=13\) becomes routine only after the pin. It is still routine.

**Product identity.** Ouyang–Wang–Huang, Corollary 5.1, states
\[
\operatorname{cr}(K_m\square P_n)=(n-1)\operatorname{cr}(K_{m+2}-e)+2\operatorname{cr}(K_{m+1})
\]
for \(m\ge 4\) and \(n\ge 1\), with \(P_n\) the path of \(n\) edges. The preserved text derives it from their Theorems 5.1 and 5.2. Those theorems use their zip-product Lemma 4.1 and Bokal's capped-product lemma. This review did not re-audit that chain. Substituting the minus-edge formula and the pinned Harary–Hill formula produces the Zheng product formula. The arithmetic for even and odd \(m\) is the candidate's Section 6 and was matched against the displayed floors. Even \(m\), and odd \(m\le 11\), then follow from the ranges already closed above. Odd \(m\ge 13\) is the image of the new odd minus-edge bound under Corollary 5.1. One substitution is one application.

## Counting, deletion, and zip do not close odd \(n\ge 15\)

`gap-check.py` recomputes the bounds in exact integers. The script and `gap-check.out` are in this directory. Both say `ALL GAP CHECKS PASSED`.

For odd \(n=2s+1\), Theorem 3.1 of Ouyang–Wang–Huang, evaluated at the pinned values, lies exactly
\[
\frac{(s-1)(s-2)}{2(2s+1)}
\]
below the target. At \(n=15\) the deficit is \(1\), so the ceiling is \(419\) and the target is \(420\). At \(n=17\) the ceiling is \(755\) and the target is \(756\). The deficit increases with \(s\). Integrality stops at \(n=13\).

Theorem 3.2, the responsibility bound, is weaker on odd order. At \(n=15\) it is short by \(105/13\). Deleting every vertex of a drawing of \(K_{2s+1}-e\), charging the two endpoint deletions at \(Z(2s)\) and the other deletions at the even minus-edge value, is short by \(90/11\) at \(n=15\). The single-vertex form \(\frac{n}{n-4}\operatorname{cr}(K_{n-1}-e)\) is shorter still. Chia and Lee, Remark 1, already describe their Theorem 1 gap as linear of size at most \(n/8\). The exact deficit above has that order.

The pinned even-from-odd reduction for \(K_n\) deletes vertices and uses the odd complete graph. Run in the other direction, it is the vertex average just computed, and it stays below the target. Restoring the missing edge by the Ouyang–Wang–Huang path construction is Theorem 3.1 itself.

The zip product in Corollary 5.1 expresses the path product in terms of a larger minus-edge graph. It does not determine \(\operatorname{cr}(K_{2s+1}-e)\). Asiri, Burdett, Chimani, Haythorpe, Newcombe, and Wagner, LIPIcs GD 2025, prove a finite computational criterion for \(G\square P_n\) and run it on connected graphs of order 5 and 6, with a partial extension to order 7. Their Section 5 leaves the six-vertex graph of survey index 156 to Zheng, Lin, Yang, and Cui. The paper contains no theorem for arbitrary complete order.

Restricting the pinned test space to the polynomials that vanish on both slots also misses the integer. That intersection has dimension \(\binom{s}{2}^2-2\binom{s}{2}+1\) when the two evaluations are independent except for the one compatibility condition at \((t_a,t_b,t_a,t_b)\). The target dimension is \(\binom{s}{2}^2-\binom{s}{2}\). The shortfall is \(\binom{s}{2}-1\), which is \(20\) at \(s=7\). A lower bound taken from that intersection is short by a quadratic gap.

## Operation comparison with the pinned odd argument

The pinned odd lower bound is `lem:tests`, `lem:injectivity`, and `prop:odd` in the complete-graph manuscript (local lines 504, 560, and 639). The comparison is against those arguments as read, not against their titles.

**Cycle tests.** In the pinned lemma every polynomial of separate degree at most \(n-2\) is allowed. Each monomial chain is a cycle of \(K_n\) because the interpolation weights kill its boundary. On \(K_n-e\) the same chain has a nonzero coefficient on the missing pair whenever the test polynomial separates \((t_a,t_b)\) from \((t_b,t_a)\). The candidate's Lemma 3.1 cuts the test space down to the kernel of that antisymmetric evaluation on each slot, proves that the resulting chains lie in the edge space of \(G\), and only then quotes the pinned cycle pairing. The kernel step is the change. The pairing identity itself is the pinned lemma for every finite simple graph.

Lemma 3.1 proves sufficiency of those two polynomial identities. The candidate's remark, and the README sentence that the tests vanish exactly on the symmetric class, go further. The finite nonsymmetric controls show a nonzero pairing on the drawings that were tested. They do not prove that every zero pairing arises from the kernel. The proof of the theorem uses the sufficient direction.

**Split spaces and mixed orthogonality.** The pinned proposition takes both factors from one space \(\mathcal S\) of dimension \(\binom{s}{2}^2\), multiplies by the full difference product, and obtains a self-orthogonal image. That product does not satisfy the kernel condition of Lemma 3.1. The candidate therefore uses two subspaces: \(\mathcal S_a\) vanishes when the first pair is \((t_a,t_b)\), and \(\mathcal S_b\) vanishes when the second pair is \((t_a,t_b)\). Evaluation onto the symmetric polynomials in the remaining pair is surjective, so each subspace has dimension \(\binom{s}{2}^2-\binom{s}{2}\). Mixed orthogonality of the two images, under the same nonzero diagonal weights the pinned proposition uses on its crossing support, gives
\[
|\mathcal T|/2\ge\binom{s}{2}^2-\binom{s}{2}.
\]
The dimension count is ordinary linear algebra. The design is not: one space on both slots is inadmissible, and the intersection of the two subspaces is short by \(\binom{s}{2}-1\), as above. The mixed pairing is what meets the conjectured integer.

**Twisted localization.** The pinned injectivity test is
\[
H=P\,(u-v)(u-y)(v-x)\,U(x)\,V(y)\,B(u,v),
\]
with \(\deg U,\deg V\le s\) and \(B\in\mathcal P_{s-1,s-1}\). On the missing-edge graph this \(H\) does not vanish at the second slot \((t_a,t_b)\). The candidate inserts the factors \((y-t_a)\) and \((v-t_a)\) and lowers the free degrees to \(\deg V'\le s-1\) and \(B'\in\mathcal P_{s-1,s-2}\). The four separate degrees were added term by term from the displayed factors. Each sum is \(2s-1=n-2\). That arithmetic matches the text. It is not a certificate that every factor was assigned to the correct variable; that remains with the proof gate.

**Rectangular nonsingularity, away from the missing endpoints.** The pinned detector proves that the order pairing is nonsingular on \(\mathcal P_{s-1,s-2}\times\mathcal P_{s-2,s-1}\), and then records the weaker consequence for a square test space \(\mathcal P_{s-1,s-1}\). The pinned injectivity uses the consequence, at every vertex. The candidate's Lemma 3.4 uses the rectangular nonsingularity: the extra factor \(v-t_a\) moves the unknown polynomial into \(\mathcal P_{s-2,s-1}\). The square consequence does not match the reduced degrees.

The star at \(a\) or at \(b\) has \(2s-1\) spokes. The detector needs \(2s\) nodes, and the missing edge is absent, so those two vertices are not available as localization sites. The candidate isolates only the other \(2s-1\) vertices. The diagonal polynomial \(P(x,u,x,v)\) has degree at most \(2s-4\) in \(x\), and \(2s-1>2s-4\), so the root bound still forces the collision factor. The pinned argument uses all \(2s+1\) vertices against the same degree bound. The margin here is smaller, and it depends on having refused the two deficient vertices. The descent then keeps the quotient inside \(\mathcal S_a\) because \(C(t_a,t_b,y,v)\) is a nonzero polynomial in the remaining variables. The pinned descent has no side condition to preserve.

The rest of the odd lower bound is the pinned template: normalization, the cycle pairing, interpolation weights, the support inequality \(c(D)\ge|\mathcal T|/2\), nondegeneracy of a diagonal form with nonzero weights, and the dimension of an isotropic subspace. Those steps are premises or standard linear algebra inside the bridge. They do not, by themselves, produce the minus-edge count.

## Sadhu's bipartite adaptation uses different operations

Ankan Sadhu, "The crossing number of \(K_{m,n}\) with one edge deleted", ResearchGate 415807828, October 2026, CC BY 4.0. The direct PDF request returned HTTP 403. The comparison uses the author's ResearchGate text extraction, SHA-256 `b28302e25f257d230e4aef616315350e31785878b34306bca47e9804bd6162bd`, which matches the candidate's input manifest. The extraction concatenates words. The operation-bearing passages were read from that text: the abstract, the contribution paragraph, Lemma 3.2 and the start of its proof, Lemma 4.1, the three-edge replacement in the proof of Theorem 1.1, the closing rank comparison, and the further questions. The lemmas were not re-proved.

Theorem 1.1 states \(\operatorname{cr}(K_{m,n}-e)=Z(m,n)-t_mt_n\) for all positive \(m,n\), and the abstract says the argument does not assume the Zarankiewicz formula. The further questions ask about \(K_{m,n}-F\) for a set \(F\) of at least two edges, and about a matching or a star. No complete-graph statement appears in the passages read.

The operations Sadhu lists, and which the extracted proof then uses, are these.

- Lemma 3.2 is a balanced compression inequality: several rectangular factors \(A^{(i)},P^{(i)}\) of coranks \(h_i\) produce a rank lower bound with loss proportional to \(\sum h_i\). The candidate's dimension count is an evaluation kernel inside one four-variable space, not this multi-index compression.
- Lemma 4.1 extends a bipartite order map \(\Phi^{r,t}_k\) to unequal rectangle parameters and proves it is invertible on every comparison matrix. The candidate quotes the rectangular nonsingularity already proved for the complete-graph pairing. It does not extend the bipartite map.
- The proof of Theorem 1.1 replaces the missing edge \(a_1b_1\) by the signed three-edge combination \(f_{12}+f_{21}-f_{22}\), builds a completed matrix \(\widetilde J=L^TJL\), and runs the intersection identity on that completion. The candidate does the opposite with the missing pair: it forces the test chains to have coefficient zero there, and it never localizes at the deficient stars.

The two papers adapt the same pinned algebraic framework to one deleted edge in two different graphs. Sadhu's theorem does not imply the candidate's theorem. None of Sadhu's three operations is a step in the candidate. The candidate's four operations are not steps in the extracted Sadhu proof. The candidate author records having read the abstract, the introductory statement, and the closing questions. A manuscript of this package needs to cite Sadhu's theorem as the bipartite one-edge result and to say that its proof was compared at the level of these operations. No transferred lemma needs a dependency citation, because no transferred lemma is used.

## Attribution

- The Harary–Hill formula for every \(n\ge 3\) is the pinned complete-graph theorem. The even minus-edge formula and the odd cases through \(n=13\) are consequences of that theorem and of Ouyang–Wang–Huang 2014, Theorems 3.1–3.4, or of the equivalent Chia–Lee statements.
- The upper bound and the product conjecture are Zheng, Lin, Yang, and Cui, Graphs and Combinatorics 23 (2007) 327–336, as quoted by Ouyang–Wang–Huang, Lemma 2.3 and display (1.2), and by Clancy, Haythorpe, and Newcombe, arXiv:1901.05155v5, 8 December 2021, Theorems 3.12 and 3.13 and Conjecture 3.14. The same survey's Theorem 2.19 and Conjecture 2.20 attribute the minus-edge upper bound, the equality conjecture, and the cases \(n\le 8\) to that 2007 paper. The Springer DOI `10.1007/s00373-007-0726-z` returned an HTML interstitial rather than the article, so Zheng's own sentences were not read. Chia and Lee state the equality as their Conjecture 1 and prove it for \(n\le 12\).
- Clancy–Haythorpe–Newcombe v5, Section 2.2.1, says the even case follows when their Conjecture 2.3 holds for the previous order. In that survey, Conjecture 2.3 is Zarankiewicz's conjecture. Ouyang–Wang–Huang, Theorem 3.3, uses Harary–Hill for \(K_{2M-1}\). The interface used here is the Ouyang–Wang–Huang theorem, read in the preserved publisher text.
- Asiri et al., 10.4230/LIPIcs.GD.2025.20, are the 2025 computational path-product framework. Their scope, as read, is small base graphs. They do not settle arbitrary complete order.
- Sadhu is the bipartite one-edge theorem described above.

The candidate's web-search paragraph is a bounded screen. This review repeated targeted searches for a complete-graph one-edge theorem after the pin and did not find one. Absence from those searches is not a priority certificate.

## Strongest novelty objection

The odd proof is a repair of one existing machine, the pinned odd argument for \(K_n\), and a contemporary preprint shows that the same framework can be retargeted to a single deleted edge. A reader who starts from the pinned paper and asks only for \(K_n-e\) is led toward kernel conditions, smaller test spaces, and a tighter degree budget.

That objection describes the origin of the argument. It does not make the odd case a classical specialization. The pinned test space is inadmissible on \(K_n-e\). The intersection of the two vanishing conditions misses the count by \(\binom{s}{2}-1\). The square corollary of the detector does not fit the degrees that remain after the twist. The two endpoints of the missing edge cannot host the even-node detector. The counting, responsibility, vertex-deletion, and zip bounds collected above stay strictly below the target for every odd \(n\ge 15\). Those are the repairs that produce the integer \(\binom{s}{2}^2-\binom{s}{2}\). Sadhu's completion-and-compression repair solves a different graph and does not contain them.

The conjecture's age and its appearance in the surveys are context. They are not the reason for the verdict.

## Boundaries

The proof gate still has to accept the kernel argument, the degree assignment in the twisted test, the Lagrange isolation of vertices outside \(\{a,b\}\), the passage of the vanishing condition through the collision factor, and the identification of the localized pairing with the pinned detector. Finite checks in the candidate directory, including the mod-\(p\) ranks, support those identities on the instances that were run. They are not a proof. This review did not rerun them. The parent screen records a stdlib rerun whose scientific stdout matched before the shell timing footer. That rerun is also not a proof.

No Lean certificate is claimed or reviewed. No manuscript package is endorsed. The campaign count is unchanged.

## Rights

The candidate's original prose is by Myeongjin Kang, with no affiliation, under CC BY 4.0. The candidate's original code is under MIT. This review is a separate gate document in `kn-minus-edge-contribution-r1/`. Third-party texts retain their own rights: the pinned manuscripts remain under their upstream license, Ouyang–Wang–Huang and Chia–Lee and Zheng are publisher texts, Sadhu's preprint is CC BY 4.0, and the Clancy survey and the Asiri LIPIcs paper retain the licenses on those copies. No third-party file was copied into this directory.
