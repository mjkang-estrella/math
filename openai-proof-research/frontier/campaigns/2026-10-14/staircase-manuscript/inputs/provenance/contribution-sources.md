# Sources and access: staircase contribution review (Factory r1)

2026-10-14. This file accompanies `review.md`. Local file hashes and read extents are in `input-hashes.json`. The pinned OpenAI math truth at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated and was not audited. Original prose is CC BY 4.0 (Myeongjin Kang, no affiliation). Third-party rights are preserved.

## Pinned OpenAI sources (local authenticated copies; not re-fetched)

| File | Raw URL at pin | Read | Labels used |
|---|---|---|---|
| Cyclic Saxl `build/sections/dominance.tex` | https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/build/sections/dominance.tex | full | `thm:cyclic-saxl`, `prop:dominated`, `dom:pair-letter-map`, `dom:square-minimum`, `dom:noncancellation`, `dom:permutation-quotient` |
| Cyclic Saxl `build/sections/specht-tools.tex` | same prefix, `.../specht-tools.tex` | full | `lem:polytabloid`, `tools:dual-sign` |
| `sources/CONTENTS.md`, `sources/preprints-tree.json` (copies in the candidate's `inputs/context/sources/`) | — | keyword search only | item 205 (Saxl / universal tensor squares) |

## Project antecedent

- I21, `i21-signed-saxl-dominance.md` (candidate's `inputs/context` copy). Read lines 1–120, including §2.1, the repeated-row module $\cong M^\rho$ with scalar $\pm\prod r!$.

## Primary literature

| Reference | Link | Local bytes | Read |
|---|---|---|---|
| N. Harman, C. Ryba, *A tensor-cube version of the Saxl conjecture*, Algebraic Combinatorics 6(2) (2023) 507–511 | https://doi.org/10.5802/alco.267 ; arXiv:2206.13769 | `inputs/primary/harman-ryba-2023.txt` (CC BY 4.0) | full: Thm 1.1, Thm 2.4, Cor 2.5, §3 Lemmas 3.1–3.2, second proof, Remark 3.3 |
| C. Ikenmeyer, *The Saxl conjecture and the dominance order*, Discrete Math. 338 (2015) 1970–1975 | https://arxiv.org/abs/1410.6549v2 | `inputs/primary/ikenmeyer-2015.txt` | lines 200–429: §3 end, §4 (β labeling, Lemma 4.1), §5 (5.1)–(5.2) unique τ=β, §6 |
| C. Bessenrodt, C. Bowman, L. Sutton, *Kronecker positivity and 2-modular representation theory*, Trans. AMS Ser. B 8 (2021) 1024–1055 | https://doi.org/10.1090/btran/70 ; arXiv:1903.07717 | `inputs/primary/bbs-2021.txt` (CC BY 3.0 notice) | lines 255–334 (strengthened conjecture, p. 1029), 1300–1389 (§5, (5.1)–(5.2), Thm 5.2) |
| C. Bessenrodt, C. Bowman, *Splitting Kronecker squares, 2-decomposition numbers, Catalan combinatorics, and the Saxl conjecture*, arXiv:2202.03066v3 | https://arxiv.org/abs/2202.03066v3 | `inputs/primary/bessenrodt-bowman-2023.txt` | lines 1–140 (§1, Thm D), 330–479 (§3 to Remark 3.8, Thm 3.7), 1555–1579 |
| R. M. Bryant, L. G. Kovács, *Tensor products of representations of finite groups*, Bull. London Math. Soc. 4 (1972) 133–135 | https://archives.maths.anu.edu.au/people/Kovacs/K033.pdf | `external/bryant-kovacs-1972.pdf` and `.txt`, retrieved 2026-10-14; © London Mathematical Society; a local reading copy only, not for redistribution | full: Theorems 1–2, Corollary, Lemma (i)–(iii) and proofs |

## Seen only at abstract or snippet level (not relied on for statements)

- D. Benson, P. Symonds, *The non-projective part of the tensor powers of a module*, J. LMS 101 (2020) 828–856, https://arxiv.org/abs/1902.02895. Seen as an abstract or search snippet only.
- *Growth rates of the number of indecomposable summands in tensor powers*, https://arxiv.org/abs/2301.00885. Seen as a snippet only; it restates Bryant–Kovács Theorem 1 as giving a projective summand in some tensor power.
- M. Sellke, *Covering Irrep(S_n) with tensor products and powers*, Math. Ann. (2022), https://arxiv.org/abs/2004.05283. Abstract only; a complex covering statement.
- S. K. Lee, arXiv:2512.15035, **withdrawn** (the v2 comment cites mathematical gaps). Abstract page opened. Irrelevant to this package and not to be cited as a proof.
- *The Saxl conjecture and the tensor square of unipotent characters*, arXiv:2312.09157 (Algebraic Combinatorics 8(4), 2025). Search snippet only; it concerns GL_n(F_q) unipotent characters. I did not record its authors.

## Web queries actually run (2026-10-14)

1. `Saxl conjecture positive characteristic tensor cube projective indecomposable odd prime staircase`
2. `tensor power faithful module free direct summand regular module Bryant Kovács`
3. `Specht module tensor product contains regular representation direct summand symmetric group integral`
4. `"tensor cube" staircase Specht module regular representation multiplicity Harman Ryba follow-up`
5. `modular Saxl conjecture odd characteristic projective summands tensor square staircase p-core`
6. `Benson Symonds non-projective part of the tensor powers of a module free summand`
7. `Saxl conjecture survey 2024 2025 Kronecker staircase tensor square progress modular characteristic`
8. `"free orbit" OR "regular submodule" tensor product polytabloids Specht lattices integral splitting Z[S_n] summand`
9. `Sellke "Covering Irrep(S_n) with tensor products and powers" regular representation`

None of these searches returned a positive-characteristic or integral regular-summand statement for staircase tensor powers. This negative result is bounded by these queries and by the sources read above.
