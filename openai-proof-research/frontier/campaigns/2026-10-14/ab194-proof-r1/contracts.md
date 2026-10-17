# AB194 proof review r1 — exact contracts and read extents

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Paths are relative to `frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r10/`. Source pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Blob identity was checked against the complete `sources/preprints-tree.json` (sha256 `eeecc1da…09b`, `truncated=false`).

## Read completely
- `rank-isolation.md` (frozen proof), `scope.json`, `manifest.json`, `verify.py` (executed with the external anchor), `checkpoint.md`, `reading-and-comparison.md`, `source-receipt.json` (blobs cross-checked).
- `private/complex.tex` lines 1–643, all of it: standing hypotheses l.16–35, thm:complex l.55–80, lem:acyclicity with proof l.87–125, lem:complex-graded-comparison with proof l.148–214, lem:complex-twist-maps with proof l.255–299, lem:complex-euler-comparison with proof l.314–458, lem:complex-root-bundle with proof l.468–526, and the final sign/leading-coefficient proof l.530–643 including eq:complex-root-positions, eq:complex-positive-chi and eq:complex-sum-estimate.
- `private/charp.tex` lines 1–313, all of it: lem:ma-hk, thm:positive-characteristic, def:short-complex, eq:dutta-h0, and the complete cor:dutta-domain with proof.
- `private/lengths.tex` lines 1–482, all of it: thm:length-inputs, lem:normalized-limit, the char-p construction, lem:perfection-conductor, eq:perfection-hk, Koszul length zero, and lem:perfection-finite-length with proof. The mixed-characteristic subsection was read but not used.

## Read partially
- `private/reductions.tex` lines 1–95 (lem:residue-extension with full proof; start of lem:reduction) and 131–188 (end of lem:reduction proof; statement of prop:setup). prop:setup's proof is not used and was not read.
- `private/main.tex` lines 150–260 (introduction: short complexes, the uniform estimate, the Dutta consequence). The rest was not read and is not used.
- Context only, not a proof input: `frontier/NEW-TEN-2026-10-14.md` lines 1–40 and the last 25 lines; a grep of TEN-FINDINGS.md and TWENTY-FINDINGS.md for Lech/Dutta/Ulrich/AB194 (no hits in those two); a listing of `review-entry-parent/`. The r15/r17 briefs were not reread. They bear on contribution/history, not on proof correctness.

## Not read
- charzero.tex, mixed.tex body, the SmallCM companion, and the IMW primary PDFs/texts. The proof does not depend on them. IMW §4.17 (existence of the Dutta limit), Ma Thm 2.4 and BHM Thm 5.2 are used only as cited by the stipulated source and were not opened.

## Imported contracts (as used in review.md)
| Label | Exact use |
|---|---|
| thm:complex hypotheses | λ additive, λ(0)=0, colimit stability; μ∈(0,∞); λ(C/J_a)=a^hμ; positive Koszul λ-length 0; F finite free in 0..h, contractible off V(I) |
| lem:acyclicity | λH_j(F)=0 (j>0), λH_0 finite |
| lem:complex-graded-comparison | cohomology of V(t) on E ≅ cohomology on P^{h−1}_{C/I} mod length 0, finite |
| lem:complex-twist-maps | D(j+M)→D(j) zero on 𝓗 for M≥M_D, every j; finite length (D=F_Y⊗V or G⊗V) |
| lem:complex-euler-comparison | χ_λ(F_Y⊗V)=rank V·λH_0(F) when alternating rank is 0 |
| lem:complex-root-bundle | any strictly decreasing integers r_j: rank (h−1)!, single degree #{r_j>a}, Euler polynomial ∏(a−r_j), base change, on E mod length 0 |
| eq:complex-sum-estimate | 0≤(h−1)!λH_0+μΣ_k(−1)^k b_kΣ_{l=−ks}^{−1}∏(l−r_j), independent of root positions |
| thm:length-inputs | complete domain, dim>0, perfect residue field ⇒ C=D_perf, λ with μ=e((z),D) |
| lem:perfection-finite-length | λ(C⊗M)=lim q^{−h} length Φ^n(M) for finite-length M, when the limit exists |
| eq:dutta-h0 | χ_∞=lim p^{−nd} length H_0(Φ^nF) (Roberts via Ma Thm 2.4) |
| cor:dutta-domain proof | reduction ideal/c, contractibility transfer, prime filtration, BHM 5.2 low-dimensional bound, D_j⊗Φ^n=Φ^n(D_j⊗·) |
| lem:residue-extension | flat local R→S, mS=n, algebraically closed residue field, same Hilbert–Samuel function |
