# Family317: operative screen and exact prism limitation

No full target is frozen or nominated. The source already establishes the proper combinatorial Thomason model structure and Quillen equivalence to spaces on every strict globular n-category,1≤n≤ω, with unrestricted attaching targets. Weak equivalences are Street-nerve weak equivalences; fibrations are detected by Ex²N. Ordinary finite-dimensional variations, homotopy-category equivalences and formal diagram transfers are not new constructions.

A Cartesian monoidal repair is not a viable universal target: dimension1 is already ruled out by the corrected primary Pavlov paper, arXiv2208.02954v4, Propositions4.1–4.3. That entire section was read. The explicit cube example has A=[1]^3\{111}, C=A\{000}, D=A⊔_C A with nerve S², while E=D⊔_A[1]^3 is contractible. It is an actual categorical pushout, not a pushout of nerves. The argument rules out ANY Cat model structure with Thomason weak equivalences being Cartesian. Its ordinary monoid/enriched-category results do not restore the failed pushout-product axiom.

Version chronology matters: the initially downloaded arXiv2208.02954v1 falsely claimed Cartesian compatibility; that body is retained as superseded, not used as a theorem. The arXiv history identifies v4 as matching the journal version except formatting/style. The current introduction and §4 were then read directly, and §3 plus the monoid filtration/attachment proof in §5 were inspected. No conclusion uses the superseded v1 claim.

Genuine discrete-group equivariance initially looked like a missing fixed-point/composite interface. The source's actual stationary cylinders and labelled covers, however, give the orbitwise fixed-NERVE comparison in equivariant-attachment-assessment.md. This avoids asserting fixed points preserve arbitrary higher-categorical pushouts. It is a technical adaptation of the existing local machinery, not a substantial nominee.

The algebra-object direction has a different issue. Pavlov's ordinary monoid proof contracts the intermediate neighborhood W=A×[1] by the canonical retraction to A and an ordinary natural transformation back to identity, then extends it through the word filtration. One cannot simply apply c_n N to that transformation and regard it as a right Gray cylinder in higher dimensions. The following exact elementary calculation isolates the problem.

Let E=[1]×[1] with vertices a=(0,0),b=(1,0),c=(0,1),d=(1,1), ordered coordinatewise. Let A be its bottom row{a<b}, let f(s,t)=(s,0), and let g=id_E. Then f≤g and f=g on A. On the top edge[c,d], a proposed direct right-Gray prism with the canonical vertical edges would have 2-chain boundary

    [b,d] − [a,c] − [c,d] + [a,b].

In the normalized directed chain complex of N_ord(E), the only nondegenerate2-simplices are

    T1=[a,b,d],    T2=[a,c,d],

with boundaries

    dT1=[b,d]−[a,d]+[a,b],
    dT2=[c,d]−[a,d]+[a,c].

Every positive2-chain is αT1+βT2 with α,β≥0. Its diagonal coefficient is−α−β. The required prism boundary has diagonal coefficient0, so α=β=0, which cannot yield its four nonzero outer-edge coefficients. A signed chain T1−T2 has the required boundary, but is not positive. Thus the proposed positive directed-chain prism does not exist with these prescribed endpoints and edge components.

Equivalently, in c_n N_ord(E) for n≥2 the two generating2-cells compare the diagonal path with the two distinct outer paths in the same direction. They supply no2-cell between the two outer paths in either direction. There are no nondegenerate simplices above dimension2 to add a relation, and no nontrivial horizontal whiskering is possible between the minimal vertex a and maximal vertex d beyond these paths. In dimension1 reflection identifies the two outer paths through the diagonal, which is precisely why the ordinary natural transformation is available there.

This calculation does NOT refute the source couniversality theorem. The source imposes a constant-upper-map condition on its positive prism, then uses two local cylinders and sieve-cover gluing; g=id on this new row is not constant. In this very square a different source zigzag exists, since the new row has a greatest element. Nor does this calculation disprove the existence of higher monoid model structures. It refutes only the literal lift of the canonical one-step ordinary contraction with the specified components.

For arbitrary algebra/word attachments, a replacement must control compatibility across words that use both local cover pieces. A word can contain letters from each piece, so the source's two-piece nerve cover is not by itself a cover of the free algebra. Symmetric/commutative words introduce an additional quotient issue. No compatible global replacement or complete transferred algebra model structure is proved here. These are precise unpaid interfaces, not a selected weakened target and not impossibility statements about all constructions.
