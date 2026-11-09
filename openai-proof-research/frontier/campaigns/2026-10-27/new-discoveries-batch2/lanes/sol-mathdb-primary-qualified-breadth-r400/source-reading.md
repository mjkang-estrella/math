# Selected primary reading

All PDFs were saved and their exact URL, UTC, byte size and SHA256 written to source-provenance.json before pdftotext extraction or reading. No AIM host request was made. Original workshop definitions, internal examples and surrounding qualifications remain unavailable. Search snippets were routing leads only, not proof bodies. Two retained PDFs, three selected record reads, one record with selected proof-section reads; no complete dependency audit.

## 386345: full literal target already covered

Primary: Marcus Michelen and Sean O'Rourke, arXiv:2310.16966v2, internal date 4 April 2024. Read pp.1–4 definitions, examples, Conjecture 1.1, Theorems 1.2 and 1.4, then pp.4–5 deterministic dominance proof and pp.8–9 Rouche bound and concluding proof of Theorem 1.4. Middle probabilistic lemmas were not fully audited. This is selected proof reading, not a line-by-line whole-paper verification. No final journal version correspondence independently verified.

The theorem explicitly permits every alpha in (0,1), a single bounded monotone coefficient sequence independent of n, and standard Gaussian randomness. Hence alpha=epsilon covers the entire requested interval (0,1/2). The source explicitly identifies its conjecture as the AIM random-polynomial workshop problem. Its construction has block endpoints m_j=2 floor(j^(1/alpha)) and c_k=exp(-2^j) on each block; the exponent is 2^j, not 2j. The proof reduces root counts to twice a sign-change count with polylogarithmic error except on an event of overwhelming probability. Because the total root count is at most n, the exceptional event contributes o(n^alpha) to expectation. The number of blocks is asymptotic to (n/2)^alpha; for fair Gaussian signs, expected sign changes are half the number of transitions. These calculations explain why a high-probability statement really supplies the expectation endpoint; no abstract-as-proof inference is used.

This is an exclusion from new-discovery investment, not a newly credited corollary, not a full dependency audit and not registry clearance. No smaller construction is sought.

## 386320 and 386323: model definitions before investment

Primary author review: Guido Montufar, arXiv:1806.07066v1, internal date 19 June 2018, independently hosted at University of Florida course-reading URL. Read Section 3 equation (5) and product-mixture interpretation, Section 7 KL objective definition, Section 8 Theorem 16 with its determinant regions and discussion, Section 9 question 10. No original proof section for the cited Seigal–Montufar theorem was obtained. Publication-version equivalence of the review was not independently checked.

386320: three visible binary units, one hidden binary unit. Objective is maximum over all target distributions of infimum KL divergence to the model. The review calls this the first open case in its 2018 version. This is historical status only. A parity candidate cannot bound every target from above; a local likelihood solver cannot certify even the inner global optimum. No numeric sweep was run. A current search surfaced Evidence Press /releases/rbm31-exact-kl-radius/ and an OpenTorus page discussing the same endpoint. These are unverified later public leads: neither their proof body nor chronology was checked, so no discovery proposal or current open-status claim is warranted. No GitHub route was requested directly.

386323: Theorem 16 describes six regions, each requiring two parallel 2x2 determinant signs to agree. The review reports equality with mixtures of three product distributions. For normalized nonnegative 2x2x2 tensors, such a mixture is precisely a nonnegative rank-at-most-three decomposition: normalize each nonzero product factor and absorb its mass into a mixture coefficient; conversely each product distribution is rank one. Zero tensors are handled separately by scaling. Thus the review gives a concrete known-endpoint route in that format. It does not justify extending to arbitrary tensor sizes, nor certify closure/boundary qualifications of the originating proof. The publisher repository PDF timed out once; an independently addressed arXiv v2 manuscript returned 404 once. Neither route was retried. Status remains HOLD_SUCCESSOR_PROOF_GAP, not a public refutation or new result.

## Other record-level checks

386052: H=G=G_m makes K_H(p^n)=Z_p^* at every level. A smooth nontrivial finite character on Z_p^*, extended to Q_p^* by assigning p value 1, is a one-dimensional admissible representation with no fixed vector. This is an unrestricted-domain diagnosis; no source-qualified novelty or credit is claimed.

385915: f identically 1 gives one color word at each length. This only diagnoses missing source nondegeneracy; no eligible counterexample proposal.

386429: under continuous iid edge weights all 112! orderings of the 112 edges of the 8x8 grid are equally likely. For a specified spanning tree, impose each tree-path edge before the corresponding non-tree edge. Counting linear extensions gives its exact MST probability. A global maximizer requires comparison across all spanning trees or a structural optimality certificate; a small numerical search cannot provide that. Atomic/tied edge laws need additional conventions. No enumeration was run.

No scientific conclusions are inferred from failed access. No formal chain, circulant continuation, Lean file or manuscript was produced.
