# Literal-to-source algorithm map: 339209

The complete original JSONL is inputs/originals/339209.jsonl (SHA510850ae259468bb28ae902bf6d6c181e3fd2586aff3c290e922baa89e92f15d). It leaves D_(G,ell) and the algorithm implicit, so neither the title nor an arbitrary Laplacian helper defines the endpoint. The binding is the copied actual PDF inputs/sources/path.pdf, SHAac3959d30dbb35804c40679dbe6b3023b7e090253ec543fd8801c0e6be3c511e. A fresh local pdftotext extraction equals the copied text exactly. These are source-processing operations, not mathematical execution.

| Literal item | Actual source | Reviewed translation |
|---|---|---|
| P_n cells | Definition2.1 and section2 p3 | connected simple undirected path; cells1,...,n, n positive; n=1 allowed |
| Common cell type | p3 common V=R^k, P=V^n | k renamed d, positive; no scalar-only restriction |
| D_(G,ell) | Definition2.2 p3, equation1 | common arbitrary odd g:V->V and arbitrary linear operator h:V->V; h is not a scalar coupling constant |
| invariant subspace | last paragraph Definition2.2 p3 | real linear W with f(W) subset W for EVERY vector field in the class; not merely an eigenspace for one field or a flow claim without regularity |
| scalar Laplacian | Example2.3 equation4 p4 | L=D-A; h=identity gives -L; sign harmless for linear W, quotient formulas use +L |
| normal form | Proposition5.1 entire proof pp21-22; Theorem5.2 statement p22 | known general synchrony/matched-partition necessity; independently reproved by matrix units and cubic test; this is not by itself path completeness |
| previous example | Example6.3 pp26-28 | start with all basic G_q, E_q (odd q>=3), O_q (all positive q), then use every positive factorization n=qk |
| G basics | p27 | q independent vectors; no repeated or constrained parameters inside G_q |
| E basics | p27 | E_(2s-1)=(a1,...,as,...,a1), s>=2; source's word-length q is NOT proof's initial-new-class count q |
| O basics | p27 | O1=0; even length2s and odd length2s+1 have antisymmetric signed halves, zero at the odd center; independent positive-half vectors |
| concatenation | p27 | S,reverse S,S,... with shared parameters across blocks; exactly k whole blocks, no arbitrary truncation or independent parameters per block |
| completeness | Conjecture6.4 p28 | both directions are proved in INDEPENDENT-PROOF.md; labels balanced/exo/odd are supplementary, not a change of invariant class |
| material Figure14 | visually inspected cached page27 PNG | nine subspaces on P6: zero, constant, O2 repeated, O3 repeated, G2 repeated, E3 repeated, G3 reflected, O6, G6; black labels indicate negatives that text extraction loses; no universal inference from this example |

Source textual blemishes are separate from the algorithm: p27 writes P_kr where q is the declared basic length; context and n=qk resolve the dummy-letter inconsistency. The p28 O1 example prints only five zeros in its P6 list; Figure14 has six, and the algorithm unambiguously concatenates six O1 blocks. We do not redefine the theorem to classify five-cell objects on P6. Neither blemish changes the basic-word algorithm. No lattice-isomorphism or uniqueness-of-output assertion is added.

The actual PDF visibly labels arXiv1805.04144v2,1Mar2019 but its first-page footer says March3,2022. Copied official metadata lists v2 revised1Mar2019 and no journal reference. These facts do NOT authenticate a journal-final statement, establish that no correction exists, or settle why the internal footer is later. Current native search identifies a2019 SIAM18(2),904-938 publication lead, but the guarded author-directory GET returned only a JavaScript shell. No final proof body was obtained. Source-final gate remains HOLD.
