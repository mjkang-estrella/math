# Independent contribution review: integral staircase regular summand

**Verdict: SUBSTANTIAL, narrowly, for the one package as stated.** The verdict attaches to the abstract conclusion that $\mathbb Z[S_N]$ is a split summand of $(S^\rho_{\mathbb Z})^{\otimes3}$, and therefore $A[S_N]$ is a split summand of $(S^\rho_A)^{\otimes3}$ for every commutative unital ring $A$. Its new mathematical content sits in characteristics $p\le N$: regular multiplicities in characteristic 2, and every odd $p\le N$, including $p\le 2m-1$, where the staircase Specht module is not projective. The mechanism is not new. The retraction is the classical Bryant–Kovács separating-vector criterion (1972), applied with Ikenmeyer's triangular uniqueness (2015) and the pinned source's square-deficit step. The specified generator is not a separate contribution. The margin over "technical" is small, and the manuscript must state the attributions in "Conditions attached to this verdict" below.

Myeongjin Kang, no affiliation, 2026-10-14. Original review prose: CC BY 4.0. Original review code (`coordinate_controls.py`): MIT. Third-party material keeps its own rights. The saved Bryant–Kovács PDF in `external/` is a local reading copy only and is not relicensed.

This is a contribution gate only. It awards no acceptance and no count. The campaign stays at 2/10. No shared files were edited, nothing was staged or committed, nothing was uploaded, and no subagents were started.

## 1. Frozen input and full target

- `fresh-algebra-discovery-r1/candidate.md`: read in full (151 lines), 17,969 bytes, SHA-256 `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179`. This matches the brief.
- `fresh-algebra-discovery-r1/output-manifest.json`: SHA-256 `79b0fcddd7d33b980d07a951b5152ecc6a1c19e5fe8d5f3bb5e7464562f4dec9`, which matches.
- Proof gate: `staircase-proof-r1/review.md` SHA-256 `85cdaff7…e549e80`, manifest `192f9baa…f9bbba5`, and `staircase-parent/proof-disposition.json` (PASS, full scope, no repairs). All three were read. I rely on the PASS for validity. I did not repeat the full proof review.

The complete reviewed target follows. For every $m\ge1$, put $N=m(m+1)/2$ and $\rho=(m,\dots,1)$. Let $z_m=v_R\otimes v_R\otimes v_C\in L_m=(S^\rho_{\mathbb Z})^{\otimes3}$. Then $I_m:\delta_g\mapsto gz_m$ has the explicit $\mathbb Z[G]$-linear left inverse $P_m=J_m^{-1}\pi_Dq^B$. Hence the $N!$ translates form a basis of a split regular $\mathbb Z[G]$-summand, and the same orbit gives a split $A[G]$-summand after every commutative unital base change. I judge this as one package and do not narrow it.

## 2. The retraction is a single coordinate functional

Let $\beta(i,j)=m+2-i-j$ (Ikenmeyer's labeling) and $b_0(i,j)=j$. The local map $q$ kills a cell unless $a=c$. It then outputs $f_{(a+b-1,a)}$, and from that output $a$ and $b$ are recovered uniquely. Every word in the retained orbit is $w\circ g^{-1}$, so its $q^B$-preimage among basis triples is the single triple $(\beta,b_0,\beta)\circ g^{-1}$. Therefore

$$
P_m(x)=\sum_{g\in G}\theta^{*}(g^{-1}x)\,\delta_g ,
$$

where $\theta^*$ is the coordinate functional of the basis triple $\theta=e_\beta\otimes e_{b_0}\otimes e_\beta$. The content projection $\pi_D$ and the alphabet $U$ are only a convenient way to write this. The identity $P_mI_m=1$ is equivalent to

$$
c_R(\beta\circ g)\;c_R(b_0\circ g)\;c_C(\beta\circ g)=\delta_{g,1}\qquad(g\in G),\tag{$*$}
$$

where $c_R(a)$ and $c_C(a)\in\{0,\pm1\}$ are the word coefficients of $v_R$ and $v_C$. Since every factor lies in $\{0,\pm1\}$, the integral and all-ring forms cost nothing once $(*)$ holds.

**This is exactly the Bryant–Kovács mechanism.** Bryant and Kovács, *Tensor products of representations of finite groups*, Bull. London Math. Soc. 4 (1972), 133–135. Their Lemma (ii) says the regular $KG$-module is a summand of $W$ iff some $w$ satisfies $w\notin\langle w(G\setminus1)\rangle$. Their Lemma (iii) says that if $u\notin\langle uR\rangle$ and $v\notin\langle vS\rangle$, then $u\otimes v\notin\langle(u\otimes v)(R\cup S)\rangle$, with the product endomorphism $\alpha\otimes\beta$ as witness. Their Theorem 1 multiplies such separating factors. In $(*)$, the three factors separate the sets where the respective coordinates vanish. Over $\mathbb Z$, the product of $\{0,\pm1\}$ coordinate functionals is the integral version of their witness. The candidate does not cite Bryant–Kovács. The manuscript must credit it, and the local map $q$ must not be presented as a new mechanism.

## 3. The combinatorics in $(*)$ is inherited

Suppose all three factors of $(*)$ are nonzero.

1. $\beta\circ g$ has the row palettes of $v_R$ and the column palettes of $v_C$. By the nested-palette uniqueness, $\beta\circ g=\beta$. This is exactly Ikenmeyer 2015 §5: in (5.2), the contraction of the row layer and the column layer has the single surviving term $\tau=\beta$, with coefficient $\pm1$ from permutation determinants (local text lines 360–409). So $g\in\mathrm{Stab}(\beta)$, the Young subgroup of the antidiagonals.
2. For $g\in\mathrm{Stab}(\beta)$, the word $b=b_0\circ g$ has row palette $\{1..m+1-i\}$ on row $i$. Because $g$ preserves $\beta$, it also takes values $\{1..s-1\}$ on antidiagonal $s$. The candidate concludes $b=b_0$ from the pinned square-deficit identity (`dom:square-minimum`). I note that this step can also be done by the same nested-palette lemma, after reindexing $(i,j)\mapsto(i,\beta(i,j))$, which bijects $B$ onto itself. The deficit argument is therefore dispensable, and the whole proof rests on one classical Ferrers-type uniqueness, used twice. Then $g$ fixes $\beta$ and $b_0$, and $(\beta,b_0)$ determines the cell, so $g=1$. The sign at $g=1$ is $(-1)^H\cdot1\cdot(-1)^H=+1$.

So the only increment is the choice of the coordinate $(\beta,b_0,\beta)$ for this triple, plus the observation that the third factor pins the first letter. That observation removes the $\prod r!$ which the pinned map $Q$ and I21 §2.1 incur when they forget $a$. Independent controls (§7) confirm $(*)$ for $m\le5$. They also show that both obvious variations fail.

## 4. What a TECHNICAL or KNOWN verdict would need, and why I did not find it

A downgrade needs a cited statement, or a short standard reduction, that gives the regular summand in every characteristic $p\le N$, or over $\mathbb Z$. I checked each route the brief names.

| Route | What it gives | Why it does not give the package |
|---|---|---|
| I21 §2.1 plus Harman–Ryba Thm 2.4 | Abstract $\mathbb C[S_N]\subset(S^\rho_{\mathbb C})^{\otimes3}$ | Characteristic 0 only. I21's map carries the scalar $\pm\prod r!$. At $m=2$, $p=2$, $M^\rho$ is **not** a direct summand of $S^\rho\otimes S^\rho$ at all (control B: the trivial module splits from $M^{(2,1)}_{\mathbb F_2}$, since the index 3 is odd, but not from $(S^{(2,1)}_{\mathbb F_2})^{\otimes2}$). So this route has a real integral obstruction, not just a missing normalization. |
| Characteristic $p>N$ | Regular summand | Semisimple. Follows from characteristic 0. Inherited. |
| Harman–Ryba §3, Remark 3.3 ($p=2$) | Every PIM $P(D)$ is a summand of the cube | A regular summand needs multiplicity at least $\dim D$ for every $D$. The argument gives at least one. Brauer-character bookkeeping does not close the gap: $\chi_\rho^3-\chi_{\mathrm{reg}}$ is a genuine character and a $\mathbb Z$-combination of the $\Phi_D$, but nothing cited makes those coefficients nonnegative. |
| Odd $p$ with $2m-1<p\le N$ (for example $m=5$, $p=11,13$) | All hooks of $\rho$ are the odd numbers $\le2m-1$, so $\rho$ is a $p$-core and $S^\rho_k$ is simple projective. HR's second proof, with the **stipulated** upstream complex Saxl theorem (catalogue item 205) in place of Lemma 2.1, then gives every PIM in the cube. This is my own reviewer deduction, recorded only to set the boundary. | Same multiplicity gap as for $p=2$. |
| Odd $p\le2m-1$ | — | The hook $p$ occurs, so $v_p(\dim S^\rho)<v_p(N!)$ and $S^\rho_k$ is not projective. HR's modular method does not apply. I found no prior statement about the staircase cube in these characteristics. |
| Integral form of HR Thm 2.4, via branching or Specht filtrations | $M^\rho\otimes S^\rho=\mathrm{Ind}_Y\mathrm{Res}_YS^\rho$ with $Y=S_\rho$. A free factor $\mathbb Z[Y]$ appears in skew-Specht filtrations. | A free factor splits off only if it is a quotient. I found no standard ordering that places it last. Even with that, the first step $S\otimes S\twoheadrightarrow M^\rho$ needs Ikenmeyer's unique-term computation. In fact the candidate's identity with $g\in Y$ *proves* $\mathrm{Res}_YS^\rho_{\mathbb Z}\supseteq\mathbb Z[Y]$ split, generated by $v_R$ and detected by $e_{b_0}^*$. This is the integral HR 2.4 for the staircase, obtained as a by-product. |
| Bryant–Kovács Theorems 1–2; Benson–Symonds (abstract only) | A regular summand in $(T\oplus V)^{\otimes(n-1)}$, or asymptotic projective parts of high tensor powers | These give no fixed power, and nothing about the cube. |
| BBS 2021 (strengthened conjecture, p. 1029; §5, Thm 5.2); BB arXiv v3 (Thm D / 3.7) | Characteristic-2 square framing; square splitting identities | These concern a different object, the square, and characteristic 2 only. |
| Sellke 2020 / Math. Ann. 2022; Luo–Sellke 2017 (via HR) | Complex covering by tensor powers | Characteristic 0 occurrence statements only. |

So the abstract conclusion is not obtained "with little additional work" from standard filtrations, branching, tensor identities, or the cited modular results. It *is* obtained with little additional work from Bryant–Kovács plus Ikenmeyer, once the coordinate $(\beta,b_0,\beta)$ is chosen. That is the whole bridge. It explains why the verdict is narrow.

## 5. Why SUBSTANTIAL rather than TECHNICAL

- **The conclusion strictly strengthens a published theorem.** Harman–Ryba (Algebraic Combinatorics 6, 2023) prove complex occurrence, and characteristic-2 PIM occurrence via projectivity. The package gives, for every field $k$, $k[S_N]\mid(S^\rho_k)^{\otimes3}$. Hence every PIM appears with multiplicity at least $\dim D$, in every characteristic, and the same holds over $\mathbb Z$. At odd $p\le2m-1$ the published method cannot work at all, and I found no antecedent.
- **The obstruction is real.** The known constructions carry $\prod r!$, which vanishes modulo every $p\le m$. Control B shows that the intermediate permutation module does not split integrally even at $m=2$.
- **The scale is publishable.** Harman–Ryba is itself a five-page note made of two short arguments. A note proving the all-characteristic, integral regular version, with one explicit generator and functional, is comparable in kind and stronger in statement.

Against these points: the proof is about one page of known ingredients. The specified generator and retraction are a choice, not a structure. A referee could reasonably call it a sharpening of Ikenmeyer §5 in the Bryant–Kovács framework. I weigh the new modular conclusions as sufficient, but only just.

What is **not** awarded:
- complex occurrence (HR Thm 1.1; the stipulated upstream Saxl theorem already gives it for the square);
- complex regular containment (I21 §2.1 plus HR Thm 2.4);
- characteristic-2 PIM occurrence (HR §3, Remark 3.3);
- triangular uniqueness (Ikenmeyer §§4–5);
- the sum-letter and square-deficit mechanism (pinned `dominance.tex`);
- the regular-summand criterion and product witness (Bryant–Kovács 1972);
- the specified-generator novelty on its own.

The verdict would drop to KNOWN/DUPLICATE if a source were found stating a free or regular summand of the staircase cube in positive characteristic or over $\mathbb Z$. It would drop to TECHNICAL if a source stated an integral free summand of $\mathrm{Res}_{S_\rho}S^\rho$ together with an integral surjection $S^\rho\otimes S^\rho\to M^\rho$. My search found neither (§8). That is a bounded negative result, not a priority claim.

## 6. Conditions attached to this verdict, and notes for the proof and manuscript gates

1. **Required attribution.** Cite Bryant–Kovács 1972, Lemma (ii)–(iii), as the regular-summand criterion and the product-witness mechanism. Present $P_m$ as the coordinate functional of $(e_\beta,e_{b_0},e_\beta)$ (§2), or at least state that equivalence. Keep the existing credits to Ikenmeyer, the pinned source, I21 and HR.
2. **Claim emphasis.** The headline should be the all-characteristic and integral regular summand, especially odd $p\le2m-1$ and the char-2 multiplicities. "Explicit generator" should be described as the proof device, not as the novelty.
3. **No real mathematical concern for proof reviewers.** Two optional remarks:
   - $S^\rho_{\mathbb Z}$ is saturated in $M^\rho_{\mathbb Z}$, because standard polytabloids give a basis over every field (James 1978, Ch. 8). So $A\otimes S^\rho_{\mathbb Z}$ agrees with the usual Specht module over any field, and over any $A$ it embeds in $A\otimes M^\rho_{\mathbb Z}$. This strengthens the interpretation of the statement. The proof does not need it.
   - The deficit step can be replaced by a second application of the nested-palette lemma (§3). This is a simplification, not a repair.
4. **Context.** The pinned upstream source stipulates the complex Saxl square theorem (catalogue item 205). The manuscript should say so wherever it describes the complex cube results as context. A withdrawn 2025 arXiv claim (2512.15035) exists. It is irrelevant to this package and must not be cited as a proof.

## 7. Independent finite controls (support only)

`coordinate_controls.py` was written for this review. It does not import the candidate's or the proof reviewer's code. Run it from this directory:

```sh
python3 -B coordinate_controls.py > coordinate-controls.json
```

- **A.** A complete backtracking search over $g\in\mathrm{Sym}(B)$ finds every $g$ with all three coordinates of $(*)$ nonzero. It prunes only by the literal block-support rule of alternating tensors and supplies no uniqueness lemma. For $m=1,\dots,5$ (with $N$ up to 15), the only such $g$ is the identity, with product $+1$.
- **Brute force at $m=3$.** All 720 permutations without pruning give one nonzero term, equal to $+1$. Dropping the column factor gives 12 nonzero translates. Replacing $b_0$ by $\beta$ in the second slot also gives 12. Both mutations are detected.
- **B.** At $m=2$ over $\mathbb F_2$, the trivial module is a summand of $M^{(2,1)}$ but not of $S^{(2,1)}\otimes S^{(2,1)}$, where each has exactly one invariant vector and one invariant functional. The pair-letter scalar $\prod r!=2$ is $0$ modulo 2.

These finite cases prove nothing for all $m$ and say nothing about novelty. I did not rerun the candidate's or the GLM checks.

## 8. Literature search and its bounds

**Read in full or in the stated extents:**
- Harman–Ryba 2023: full text.
- Ikenmeyer 2015: §§3–6, local lines 200–429.
- BBS 2021: pp. 1028–1029 (lines 255–334) and §5 through Thm 5.2 (lines 1300–1389).
- BB arXiv v3: §1 (lines 1–140), §3 through Remark 3.8 (lines 330–479), and Remarks 8.2 (lines 1555–1579).
- Pinned `dominance.tex`: full. Pinned `specht-tools.tex`: full.
- I21: lines 1–120.
- Bryant–Kovács 1972: full, three pages, retrieved for this review.
- The pinned catalogue `CONTENTS.md` and `preprints-tree.json` were searched for Saxl, staircase, Kronecker, tensor square or cube, and Specht. Only the two pinned Saxl manuscripts are relevant, and both are complex statements.

**Web searches run:**
- Saxl conjecture, positive characteristic, tensor cube, projective indecomposables, odd primes
- Bryant–Kovács, free summands in tensor powers
- Specht tensor product containing the regular representation integrally
- tensor cube, staircase, regular multiplicity, follow-ups to Harman–Ryba
- modular Saxl in odd characteristic, $p$-cores
- Benson–Symonds, non-projective part of tensor powers
- Saxl surveys from 2024–2025
- free orbit and integral splitting with polytabloids
- Sellke's covering paper

The arXiv abstract page of the withdrawn 2512.15035 was opened directly. Benson–Symonds, arXiv 2301.00885, and Sellke were seen only at the abstract or snippet level.

**Negative result, and its limits.** I found no statement of a free or regular summand in any staircase Specht tensor power in positive characteristic or over $\mathbb Z$. I also found no odd-characteristic staircase cube result. This rests on the sources and queries listed above. It does not cover all integral representation theory literature, MathSciNet, theses, or non-indexed work, and it is not a worldwide-priority claim.

Exact inputs, hashes and read extents are in `input-hashes.json`. Sources and links are in `sources.md`. My outputs are listed in `outputs.json`.
