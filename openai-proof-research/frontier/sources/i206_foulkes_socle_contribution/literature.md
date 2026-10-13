# I206 primary literature and exact reading limits

2026-10-12. Verdict: **TECHNICAL/KNOWN ONLY**, in the precise sense explained in `../../reviews/i206-foulkes-socle-contribution.md`. This is a bounded contribution assessment. It neither establishes exhaustive priority nor completes an independent proof gate. All SHA-256 values and scopes are in `../../experiments/i206_foulkes_socle_contribution/input-authentication.json`.

## Primary sources actually read

1. **Kumar–Landsberg**, *Connections between conjectures of Alon–Tarsi, Hadamard–Howe, and integrals over the special unitary group*, Discrete Mathematics 338 (2015), 1232–1238. [Author-hosted published PDF](https://people.tamu.edu/~jml/KLfoulkeshowefinal.pdf), [DOI](https://doi.org/10.1016/j.disc.2015.01.027). Read the complete existing text `../i202_foulkes_quotient/kumar-landsberg-2015.txt`, lines 1–477, all seven pages including references. No new duplicate copy.

   Proposition 1.8 was also read: its reported diagonal h_(5,5) kernel gives the p=5 consequence explained in the review; the credited unpublished calculation was not independently replayed. The relevant proofs are Proposition 2.1 (the invariant, including symmetry and nonvanishing) and Section 3 (the even-order Alon–Tarsi/Chow equivalences of Theorem 1.9). Theorem 1.9 itself assumes even order. Proposition 2.1 applies to degree p-1 forms in dimension p, and composing its invariant with D_y F recovers I202's K(F;y) up to invariant normalization. This composition and the ensuing quotient interpretation are deductions recorded in the review; they are not quotations of a socle theorem from this paper.

2. **Kotlar**, *On extensions of the Alon–Tarsi Latin square conjecture*, [arXiv:1204.5276v2](https://arxiv.org/abs/1204.5276v2), 3 September 2012; published in Electronic J. Combinatorics 19(4), #P7, [DOI](https://doi.org/10.37236/2269). Read the complete existing text `../i202_foulkes_quotient/kotlar-1204.5276.txt`, lines 1–481, all eight pages including references. No new duplicate copy.

   Read definitions in Section 1, the proof of Lemma 2.1 and Theorem 2.2, the complete orbit proof of Theorem 3.5 and Corollary 3.6, and the remaining sections. The squarefree per(X)det(X)^(n-1) coefficient is precisely I202's scalar. Normalized-unipotent and reduced-square constants are not interchanged. Proposition 4.1 is a different matrix identity with the reduced-square imbalance and is not the full K(F_L;y) identity.

3. **Drisko**, *Proof of the Alon–Tarsi Conjecture for n=2^r p*, Electronic J. Combinatorics 5 (1998), #R28. [Published PDF](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v5i1r28/pdf/), [DOI](https://doi.org/10.37236/1366). Newly retained `drisko-1998-r28.pdf` and `.txt`. All five pages, complete extracted text, read including references.

   Theorem 4 proves the odd-prime congruence by an isotopy action on fixed-diagonal squares. Its proof identifies the surviving orbit with the subtraction table over Z/p and computes its stabilizer. The fixed-diagonal count divided by (p-1)! matches Kotlar's normalization. The paper concerns Latin-square nonvanishing, not Chow quotient multiplication. Corollary 5's other orders are not used to assert an additional odd-composite family.

4. **Raicu–Sam–Weyman**, *On some modules supported in the Chow variety*, [arXiv:2108.10910v1](https://arxiv.org/abs/2108.10910v1), 24 August 2021. Read complete existing text `../i199_foulkes_structured/raicu-sam-weyman-2108.10910v1.txt`, lines 1–1061, all twenty pages including references. No new duplicate copy.

   Read the normalization theorem and its proof (Theorem 2.3, Proposition 2.7, Remark 2.9), the exact deficiency sequence, Section 3's module/resolution statements, and Section 4's examples and proofs. Corollary 4.6(a) explicitly describes the ternary-cubic quotient as det(U)^2 in degree 2. Example 4.5 supplies the Hessian relation. This is exact prior art for p=3 in dimension three, stronger there than identifying a submodule. The relation to higher dimensions follows formally as in the review; the paper is not being cited as stating the full all-prime family. Section 5 and its proof were also read; no new consequence concerning its Veronese Tor modules is claimed.

5. **Kumar**, *A Study of the representations supported by the orbit closure of the determinant*, [arXiv:1109.5996v2](https://arxiv.org/abs/1109.5996v2); published Compositio Mathematica 151 (2015), 292–312, [DOI](https://doi.org/10.1112/S0010437X14007660). Newly retained `kumar-1109.5996v2.pdf` and `.txt`. All 23 pages, complete extracted text lines 1–1222 including references, read. The retained PDF has the arXiv v2 watermark dated 15 October 2012 and a title-page date of 25 September 2018; no silent identification with a different version is made.

   Read Section 2's construction and nonvanishing, Section 3's actual restriction map, Section 4's Latin rectangles, Section 5's pairing/isotypic proofs, and Section 6's consequences. In particular, Proposition 2.3, Definition 2.5, Lemmas 2.6–2.7, Proposition 3.2, Propositions 5.2/5.5, Theorem 5.6, Theorem 6.1 and Remark 6.6 were examined in context. These results explain the established invariant/restriction bridge. They do not state the nonrectangular multiplication image or the odd-prime socle family under review.

No fresh visual PDF rendering was used: “read in full” means all extracted textual content, including displayed formula extractions and references, not independent inspection of each PDF page image. The extraction has recognizable notation artifacts; no ambiguous artifact is used to supply an essential new assertion.

## Accepted corpus and supplied records

- `AGENTS.md` and `sources/upstream.json`: full contents read. The pinned revision is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
- `sources/CONTENTS.md`: used only for orientation. A broad initial display was truncated; the Foulkes family entry was then explicitly read at lines 4789–4807. No claim of a complete catalogue reading or recursive manuscript audit.
- Existing sixth-power `build/sections/reduction.tex`: lines 1–125 and 218–304 read. These cover `eq:multmap`, the Cauchy label formula, rectangular-shift proof, `lem:polarization`, `cor:module-generation`, and the stated large-degree bound. The intervening chart subsection was not read. Accepted source results were not revalidated.
- Existing quadratic-stabilization `build/paper.tex`: lines 1–165 read, including the canonical algebra/map, `thm:main`, and its precise relation to the ordinary comparison. Remainder and included files not read. This is a companion check in the assigned family, not a truth audit.
- I202 brief, report, complete 234-line analytic record, literature record and parent disposition: read on disk. The supplied prompt's I206 brief was read as prompt text; no local-file hash is manufactured for it. No I199 task report or unrelated/live-task output was opened. The external RSW source retained under I199 was read in place.

## Search boundaries

Web searches included combinations of Foulkes, Chow normalization, socle, determinant covariant, odd prime, Alon–Tarsi, Drisko and Briand's decomposable-form covariants. Publisher/arXiv pages led to the primary sources above. Search snippets and abstract-only discoveries were not used to certify a mathematical theorem or novelty.

Brion's 1997 publisher record and a failed guessed Numdam record, Briand's 2010 chapter search result, unrelated modular Foulkes-module socle results, and other citation leads were discovery only. The Brion/Briand texts, Howe's original paper, Zappa's original paper, and classical Aronhold text were not fully read and are not claimed as independently verified sources. Their results are used only where actually stated/proved in a read source, with that attribution. No inaccessible source is claimed to contain or exclude the family.

Within the five fully read primary papers, the all-prime socle theorem and the full K(F_L;y) identity were not found verbatim. The negative search is not proof of novelty. The technical verdict rests instead on the explicit short deduction from known operations and the lack of a demonstrated substantial consequence beyond the constituent family, while recognizing the precise known p=3 case.
