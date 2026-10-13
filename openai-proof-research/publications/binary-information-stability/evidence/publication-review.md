# Publication review

2026-10-13. Author: Myeongjin Kang, Independent researcher.

Claude Opus 5.5 manuscript audit R1 found no mathematical error in the three theorems, conditional on the explicit pinned upstream inputs. Its verdict was REPAIR for missing predecessor citations and matching metadata. This is AI review, not human peer review or formal verification. Numerical checks are supporting evidence, not proofs.

P1 and P2 are resolved. Added Chen–Gohari–Nair, Chen–Gohari–Javanmard–Lin–Mirrokni–Nair–Woodruff, and Heilman–Tarter to the introduction, bibliography, and metadata. Confirmed Honghao Lin and all author initials from the primary title/abstract pages. Read Chen–Gohari–Nair Section II, including the dimension induction; Chen et al. Section 9, including the candidate definitions, Theorem 9.1, and full Lemma 9.2 and proof; and Heilman–Tarter Lemmas 5.1 and 5.3 and their proofs. These are attribution checks, not audits of those complete papers.

Primary sources: https://arxiv.org/html/2502.10019v2 ; https://arxiv.org/pdf/2609.24931v2 ; https://arxiv.org/html/2011.05583v2 . The latter journal citation and DOI were checked against its arXiv abstract record. Downloaded primary PDFs are retained under tmp/primary.

The small-information profile comparison in the introduction was checked against the Section 9 definitions after converting entropy units and generator normalization, and against the pinned flow.tex comparison. In the manuscript notation its first branch is F(psi(m)+I)-m V(s), with m H(s)=(H(m)-I)s. At I=0, s=m and s'=m/(H(m)+m V(m)). The first branch has derivative 1+m H(m)/((1-m²)V(m)(H(m)+m V(m))), which tends to 1 as m tends to 1, whereas F'(0)=2. Thus for a fixed m sufficiently close to 1 the earlier maximum equals F(I) on a positive interval beginning at zero. The added c m² I² is strictly positive there. This comparison of displayed profiles is not a worldwide novelty claim.

P3 was handled by specifying the base inequality D(u)>=F(I(u)) in the abstract. The theorem statement and all proofs are unchanged. P4 and P5 were optional; the replacement argument remains proved inline, and the existing locally defined notation is retained. No new mathematical audit round was needed for these citation and scope clarifications.

The final 15-page PDF builds without warnings, undefined references, or overfull boxes. Every page was visually inspected after revision. The flattened single-file source ZIP rebuilds to identical extracted PDF text. Final hashes and verification details are recorded separately. The AI-use acknowledgment follows the preceding publication packages and includes the requested Opus manuscript review.

All work is isolated in the publication worktree. No main research thread, original checkout, or research acceptance ledger was changed.
