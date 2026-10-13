# I202 primary literature and source boundaries

2026-10-12. All corpus theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted. Existing source copies were read in place. The retained new papers below were read completely through their text extractions; PDF hashes bind the original bytes and text hashes bind the reading representation. See `../../experiments/i202_foulkes_quotient/input-authentication.json` for exact SHA-256 values and reading scopes.

## New primary papers read in full

1. **M. Domokos**, *Vector invariants of a class of pseudo-reflection groups and multisymmetric syzygies*, J. Lie Theory 19 (2009), 507–525; [arXiv:0706.2154v2](https://arxiv.org/abs/0706.2154v2), dated 11 February 2015 in the retained PDF. Retained as `domokos-0706.2154.pdf` and `.txt`, all 23 PDF pages read via the complete extraction.

   Proposition 2.1 gives the trace-product basis with at most n factors. Theorem 2.5 gives all fundamental trace relations and the minimal power-sum generators; at n=7, q=1 its relation uses eight inputs. Theorem 3.2 bounds total degree in a finite presentation. Theorems 5.5 and the examples were also read, though no characteristic-p assertion is used here. The source supplies an exact algebra presentation, not an elementary-generator-length bound on the per-row-degree filtration. No inference from its total-degree bound to C_8=0 is valid.

2. **Daniel Kotlar**, *On extensions of the Alon–Tarsi Latin square conjecture*, Electronic J. Combinatorics 19(4) (2012), #P7; [arXiv:1204.5276v2](https://arxiv.org/abs/1204.5276v2), dated 3 September 2012. Retained as `kotlar-1204.5276.pdf` and `.txt`, all eight pages read via complete extraction. [Published record](https://doi.org/10.37236/2269).

   Theorem 2.2 identifies the squarefree coefficient of per(X)det(X)^(n-1) for odd n as (-1)^(n(n-1)/2) n!(n-1)! AT(n). Corollary 3.6 gives AT(p) congruent to (-1)^((p-1)/2) mod p for odd primes. Its modular proof, including the orbit argument, was read. AT here uses **normalized unipotent** squares. The paper explicitly distinguishes the alternative reduced-square conjecture; this attempt does not substitute that constant. These results pay the nonzero scalar in the actual determinant-multiplication identity.

3. **Shrawan Kumar and J. M. Landsberg**, *Connections between conjectures of Alon–Tarsi, Hadamard–Howe, and integrals over the special unitary group*, Discrete Mathematics 338 (2015), 1232–1238. [Author's published PDF](https://people.tamu.edu/~jml/KLfoulkeshowefinal.pdf); [DOI](https://doi.org/10.1016/j.disc.2015.01.027). Retained as `kumar-landsberg-2015.pdf` and `.txt`, all seven pages read via complete extraction.

   Proposition 2.1 constructs determinant-contraction invariants; Theorem 1.9 proves the even-order Alon–Tarsi/Hadamard–Howe equivalences. The article explains the relation between canonical kernels and Chow equations and distinguishes it from the ordinary Foulkes comparison. It is strong prior-art evidence for the method, not a proof of the full (7,8) map or a statement that the new socle packaging is novel.

## Existing sources read in place

- Quadratic stabilization corpus paper in `../i198_geometry_representation/preprints/Quadratic-Stabilization-of-the-Canonical-Foulkes-Howe-Map-September-25-2026/build/paper.tex`: full displayed file read; Section 2, `lem:shift`, `prop:vanishing`, and the comparison corollary are relevant. Included files are not implicitly part of that reading.
- Sixth-power corpus paper, `../i198_geometry_representation/preprints/Foulkes-Conjecture-for-the-Sixth-Symmetric-Power-September-25-2026/build/sections/reduction.tex`: full section read. Used `eq:multmap`, the Cauchy label multiplicity discussion, `lem:polarization`, and `cor:module-generation`. The ordinary sixth comparison does not imply the canonical seventh seed.
- Raicu–Sam–Weyman, *On some modules supported in the Chow variety*, [arXiv:2108.10910v1](https://arxiv.org/abs/2108.10910v1), existing text in `../i199_foulkes_structured/`: beginning through Section 2 and the start of Section 3. Theorem 2.3, Remark 2.9, and the displayed deficiency sequence identify the actual quotient. In their notation B_(d,n) is the present R, k[Y_(d,n)] is the present A, and their ambient R_(d,n) is neither. This attempt does not claim a fresh full reading of the regularity theorem.
- Cheung–Ikenmeyer–Mkrtchyan, *Symmetrizing tableaux and the 5th case of the Foulkes conjecture*, [arXiv:1509.03944v1](https://arxiv.org/abs/1509.03944v1), existing text in `../i199_foulkes_structured/`: opening through highest-weight-space setup. Theorem 6(b)'s genuine diagonal kernel is used only as a counterexample to a blanket symmetrizer/straightening principle. No computational verification was replayed.

The source URLs for the two corpus files are pinned raw GitHub URLs recorded in input-authentication.json. No other corpus family was opened for research.

## Search and conclusion limits

Searches for multisymmetric relations, all-slot/prolongation approaches and Foulkes–Latin-square connections led to the papers above. Search snippets for padded forms, secant prolongation, and Latin rectangles were discovery leads only; no theorem from an unread paper is invoked. A search result pointing at the moving upstream overview was not used as a pinned mathematical input.

The odd-prime socle family is a complete deduction but not certified new to literature. The actual remaining problem is A_1^2(C_6/W_7)=0, equivalently the filtered straightening or full-jet injectivity estimate in the analytic record. The retrieved literature does not settle those estimates, and no worldwide open-status claim is made.
