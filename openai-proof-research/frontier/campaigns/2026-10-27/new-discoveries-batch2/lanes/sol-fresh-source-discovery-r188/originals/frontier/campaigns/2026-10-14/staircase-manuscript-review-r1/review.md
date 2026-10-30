# Independent manuscript gate: staircase integral regular summand

**Verdict: PASS for the full manuscript.** No mathematical repair and no repair of the frozen paper is required. The paper proves the full original theorem as a standalone text: every $m\ge1$, the specified ordered tensor $z_m=v_R\otimes v_R\otimes v_C$, the explicit integral $\mathbb Z[G]$-linear retraction $P_m=J_m^{-1}\pi_{\mathcal D}q^B$, its coordinate-functional form, coefficient $+1$, and split base change to every commutative unital ring without flatness. Two conditions apply to the **final package**, not to the frozen paper (§6). Ten optional clarifications are listed in §7.

This is a manuscript gate only. It awards no acceptance and changes no count. Nothing outside this directory was edited. Nothing was staged, committed or uploaded, and no subagents were started. Frozen inputs are unchanged (§8).

Myeongjin Kang, no affiliation, 2026-10-15. Original review prose: CC BY 4.0. Original review code (`independent_controls.py`, `copy_checks.py`, `audit_inputs.py`, `make_output_manifest.py`): MIT. Third-party and OpenAI materials keep their own rights. No third-party text is copied here beyond short locators.

## 1. Frozen identity

| File | Bytes | SHA-256 |
|---|---:|---|
| `staircase-manuscript/main.tex` | 15,845 | `015e76c58ebbd6b92c8868d2de9cf49f533f18408e5017b720df8d02f4767495` |
| `staircase-manuscript/main.pdf` (6 pages) | 89,299 | `40aebbdda3c407298f499895b7cd8aee543025864efbcb94808441e1b6b6f54c` |
| `staircase-manuscript/output-manifest.json` (79 records) | 13,564 | `0fab9a185d016faca5fb035a07aa7b78ddc99dc8437e370f6499897cc989383e` |
| `staircase-manuscript/input-manifest.json` (41 inputs) | 16,849 | `bff337d335a1a14ab806414eb5f38a61c4d275dbecfdfb981f39b61a289da3c0` |
| `fresh-algebra-discovery-r1/candidate.md` | 17,969 | `6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179` |
| `staircase-proof-r1/review.md` | | `85cdaff75e27300815f81a28fc709a5714b16fa1941d023f44238b302e549e80` |
| `staircase-contribution-factory-r1/review.md` | | `47de7398e889efb726de5e993384ace4e3e1f83d095e37a68a309f5aaa64b060` |
| I21 note (internal snapshot) | | `607c2c3296b6e020d8f0ae12526ee593ba3369e00fa5c4f393e53ee5b6936b6a` |

All eight match the brief and the paper's own citation of I21. `input-manifest.json` in this directory records the bytes, hash and read extent of all 38 files this review read or authenticated. Hashes establish identity only; they certify no mathematics.

## 2. Standalone reconstruction of the paper

I read every line of `main.tex` and `references.tex` and reconstructed each step without relying on the prior proof PASS. Section and equation numbers below are the paper's.

### 2.1 Theorem 1 matches the original target

Theorem 1 quantifies over every $m\ge1$, fixes $N$, $\rho$, $B$, $G=\mathrm{Sym}(B)$, uses the exact $z_m$ with the block orders of §2, names $P_m$ in (3.2), asserts that the $N!$ translates are a $\mathbb Z$-basis of a split regular summand, and gives the split $A[G]$-embedding for every commutative unital $A$ with "No flatness or characteristic assumption". There is no narrowing to complex occurrence, a prime range, small $m$, or a substitute generator. $q$, $\mathcal D$, $\beta$, $b_0$ and $w$ in §3 are exactly the original data.

### 2.2 Words, polytabloids and the common lattice (§2)

- **Signs of `alt`.** A term $\sigma$ puts letter $\sigma(k)$ at $d_k$ with sign $\mathrm{sgn}\,\sigma$. Each nonzero word coefficient is $\pm1$, and it is nonzero exactly when every block uses $\{1,\dots,r\}$ once. Correct.
- **Tabloid map.** A tabloid goes to the word with letter $k$ on row $k$. For $\{gt\}$ the letter at $x$ is the row of $g^{-1}x$ in $t$, so this word is $a\circ g^{-1}$. The bijection onto the content-$\rho$ words is therefore equivariant for $ge_a=e_{a\circ g^{-1}}$. Letter $k$ occurs $m+1-k=\rho_k$ times, as required.
- **Tableaux.** In $t_R$, entry $(i,j)$ sits in cell $(j,i)$. Column $i$ is $(i,1),\dots,(i,m+1-i)$ from top to bottom, which is $R_i$, and the row word is $j$. In $t_C$, column $j$ is $C_j$ and the row word is $i$. Both shapes are $\rho$, because $\rho^t=\rho$.
- **Polytabloid equals `alt`.** For $h$ in the column group, the word of $h\{t\}$ is $a_t\circ h^{-1}$. On a column $(d_1,\dots,d_r)$ this assigns $\sigma(k)$ to $d_k$, where $h^{-1}d_k=d_{\sigma(k)}$, and $\mathrm{sgn}\,h=\mathrm{sgn}\,\sigma$. So $e_{t_R}\mapsto v_R$ and $e_{t_C}\mapsto v_C$ exactly, with no normalization. This is the paper's "inverse, with the same sign".
- **Common lattice.** Since $ge_t=e_{gt}$ and every tableau of shape $\rho$ is $gt_R$ and $gt_C$ for unique $g$, both orbit spans are the $\mathbb Z$-span of all polytabloids. This is equality of the embedded lattices, not an abstract isomorphism.
- **Cube embedding.** $S^\rho_{\mathbb Z}\subset T$ is finite free. Tensoring the inclusion successively with free (hence flat) groups gives $L_m\hookrightarrow T^{\otimes3}$, with no saturation assumption.

### 2.3 Retraction and its coordinate form (§3), on all triples including zero outputs

$q$ sends each basis triple to one basis letter or to $0$, never to a combination. The output $f_{a+b-1,a}$ is valid, since $1\le a+b-1\le2m-1$. $q^B$ and $\pi_{\mathcal D}$ are equivariant. $w(i,j)=(m+1-i,\beta(i,j))$ lists $(r,r),\dots,(r,1)$ on the row of length $r=m+1-i$. So $w:B\to\mathcal D$ is a bijection, $W_{\mathcal D}$ has as basis exactly the bijections $B\to\mathcal D$, and $G$ acts on them freely and transitively. Hence $J_m$ is an isomorphism of left modules, labelled by $g$ and not by $g^{-1}$.

**Equivalence (3.3).** For any basis triple $t$, $J^{-1}\pi q^B(t)$ is either $0$ or $\delta_g$, where $q^B(t)=ge_w$. For $(r,a)\in\mathcal D$, the only $q$-preimage of $f_{r,a}$ is $(a,r+1-a,a)$, and these letters are always valid because $a\le r\le m$. So $ge_w$ has the single basis-triple preimage $g\theta$. Triples with $a\ne c$ somewhere, or with output outside $W_{\mathcal D}$, go to $0$ under both formulas, since no such triple has the form $g\theta$. By linearity, (3.3) holds on all of $T^{\otimes3}$, hence on $L_m$. Finally, $\theta^*(gz)$ is the coefficient of $g^{-1}\theta=(e_{\beta\circ g},e_{b_0\circ g},e_{\beta\circ g})$ in $z$, which gives the product form (3.4). The paper's argument is complete. It is also more than a check on the generator: it proves the identity on every basis triple, including the zero outputs.

### 2.4 Unique surviving term (§4)

- **Deficit step versus coefficient ring.** A retained term has $a=c$ and output a bijection onto $\mathcal D$. Value $r$ occurs $r$ times as a first coordinate, so $\sum d^2=\sum r^3$. On a row of length $r$, $\sum d=r(r+1)-r=r^2$ and $\sum(d-r)^2=\sum d^2-2r\cdot r^2+r\cdot r^2=\sum d^2-r^3$. Summing over the one row of each length gives a sum of integer squares equal to $0$. The argument concerns integer labels of individual support terms, not cancellation or positivity of ring coefficients, and the paper states exactly this.
- **Palette lemma.** Letter $m$ must be in column 1. Inductively, letter $m-k+1$ cannot go to an earlier occupied position or to a column $j>k$, whose maximum is $m+1-j$. Deleting the top row removes the maximum $m+1-j$ from column $j$ and leaves the triangle for $m-1$ after reindexing. So the solution is unique and equals $\beta$, and $\beta$ satisfies all palettes. The base case $m=1$ and the empty column at $j=m$ are harmless.
- **Uniqueness and existence.** $a=c=\beta$, so $b=m+2-i-\beta=j=b_0$. The converse triple satisfies every block palette and maps to $w$. There is exactly one surviving term, not a factorial family.
- **Sign.** Layer 1 reverses each row, giving $(-1)^{\binom r2}$ per row. Layer 2 is the identity on each row, consistent with the GLM correction that $b_0$ is not a reversal. Layer 3 reverses each column, and the column lengths are again $m,\dots,1$. The product is $(-1)^H\cdot1\cdot(-1)^H=+1$.

### 2.5 Split map and base change (§4, proof of Theorem 1)

$P_m(gz_m)=J^{-1}(ge_w)=\delta_g$, so $P_mI_m=\mathrm{id}$. Hence $L_m=\mathrm{im}\,I_m\oplus\ker P_m$, and the translates form a $\mathbb Z$-basis of the image. Applying $A\otimes_{\mathbb Z}-$ to an equation between composites gives $(1\otimes P)(1\otimes I)=\mathrm{id}$ for every $A$, including nonflat $A$ and the zero ring. The identifications $A\otimes\mathbb Z[G]=A[G]$ and $A\otimes(S\otimes S\otimes S)\cong S_A\otimes_AS_A\otimes_AS_A$ are canonical and equivariant, and neither needs flatness. Nothing is inverted and no field-level injectivity is used. The proof never applies tensoring to an injection after base change.

### 2.6 Modular, multiplicity and projectivity statements (§1)

- **Multiplicities.** Over a splitting field, $k[G]\cong\bigoplus_DP(D)^{\dim D}$. A direct summand $k[G]$ of the cube gives each $P(D)$ multiplicity **at least** $\dim D$ there, by Krull–Schmidt. This holds in every characteristic, because a splitting field exists in each one. The text is correct. Its phrase "supplies these multiplicities" means lower bounds (optional wording, §7). The paper's $S^\rho_k$ is *defined* as $k\otimes S^\rho_{\mathbb Z}$, so the statement is internally exact. Identifying it with James's field Specht module is standard but not stated (optional).
- **Non-projectivity at odd $p\le 2m-1$.** The hook length at $(i,j)$ is $(m+1-i-j)+(m+1-j-i)+1=2(m+1-i-j)+1$, which runs over all odd numbers up to $2m-1$. If $p\le2m-1$ is an odd prime, the hook $p$ occurs, so $v_p(f^\rho)<v_p(N!)$. A projective $kG$-module has dimension divisible by $|G|_p$, so $k\otimes S^\rho_{\mathbb Z}$ (of dimension $f^\rho$) is not projective. The argument uses only the dimension, so it applies to the paper's module directly. Control C7 confirms the hook list and the divisibility pattern for $m\le15$: failure exactly at odd $p\le2m-1$, and equality at $p=2$ and at odd $p>2m-1$.
- **Scope of comparisons.** Char-2 PIM occurrence is attributed to HR and is not claimed. "Regular multiplicities are stronger" is correct. No claim is made about exact multiplicities, or about whether the regular summand is new at $2m-1<p\le N$.

## 3. Source interfaces and citations, checked against the actual text

| Paper's claim | Source checked | Result |
|---|---|---|
| BK Lemma (ii)–(iii): field criterion and product witness. The field proof uses injectivity of the regular module. | BK 1972 full text: Lemma (ii), proof "the regular KG-module is injective"; Lemma (iii) with $\alpha\otimes\beta$; Bull. LMS 4 (1972) 133–135 | Exact. Their witnesses are $K$-endomorphisms over a field. The paper's (3.4) factors are integral coordinate functionals, and the paper does not transfer injectivity to $\mathbb Z$. "Realize the witness" is a fair description. |
| Ikenmeyer §§4–5, eq. (5.2): triangular labeling and uniqueness | arXiv v2 text, §4 ($\beta=n+2-r-c$, l. 294–303) and §5 ((5.2), unique $\tau=\beta$, l. 360–409) | Exact for arXiv v2. Ikenmeyer argues upward from the bottom row; the paper's top-down proof is independent and is labelled "after Ikenmeyer". |
| HR Thm 1.1 complex cube coverage; §3 and Rem. 3.3 every PIM in char 2; Thm 2.4 with $C(\rho)=(1^N)$ | HR full text: Thm 1.1, Def 2.2, Ex 2.3, Thm 2.4, §3, Rem 3.3 | Exact. HR work over an algebraically closed field of char 2, matching the "splitting field" framing. |
| BBS §5 modular approach; the strengthened conjecture concerns the square | BBS p. 1029 (Strengthened Saxl Conjecture: square, char 2) and §5 (Thm 5.2) | Accurate. HR say they follow BBS's approach. |
| BB Thm 3.7, "different multiplicity question" | BB arXiv v3 Thm 3.7: $sg(\lambda,\rho)-ag(\lambda,\rho)=\delta_{\lambda\rho}$ | Accurate. |
| OAI §§2–3: ordered blocks, `dom:square-minimum` in §3; pair-letter scalar $(-1)^H\prod r!$; Theorem 3.1 `thm:cyclic-saxl` | Pinned `dominance.tex` (full), `specht-tools.tex` l. 33–100, pinned `paper.tex` (section order: intro, specht-tools, dominance; counter `[section]`; no earlier theorem-type environment in §3) | Labels, section numbers, "Theorem 3.1" and the scalar (`dom:noncancellation`) are all exact. Wording nit: the source *proves* Theorem 3.1, and this project *stipulates* it (§7, O1). |
| Universal companion treats universal complex squares | Companion `introduction.tex` thm:main | Accurate. |
| I21 §2.1 identifies $\mathbb C[G](v_R\otimes v_R)$ with $M^\rho$ via the pinned $Q$ | I21 l. 1–140, §2.1 ($\Phi$ injective, $Z\cong M^{\rho_m}$, scalar $c_m$) | Accurate, hash matches. C8 confirms 1, 3 and 60 independent translates at $m=1,2,3$, with scalars $1,-2,12$. |

**Complex antecedent.** The paper says complex regular containment follows from I21 §2.1 and HR Thm 2.4. That is correct. In fact the public pinned source alone gives the surjection $\mathbb C[G](v_R\otimes v_R)\twoheadrightarrow M^\rho$ (`dom:permutation-quotient`). Semisimplicity and HR Thm 2.4 then give complex regular containment without I21; I21 only upgrades the surjection to an isomorphism. This makes the antecedent even more clearly known and publicly checkable. It does not change the contribution boundary, which already excludes complex regular containment.

**Bibliography.** BK, Ikenmeyer (Discrete Math. 338 (2015) 1970–1975, consistent with HR's reference list), HR (doi 10.5802/alco.267, pp. 507–511), BBS (TAMS Ser. B 8 (2021) 1024–1055, doi 10.1090/btran/70), BB arXiv:2202.03066v3 (dated 18 Jan 2023), and the OAI pin `fd4aeeb2…eeeb` all agree with the reading copies and `sources/upstream.json`. No withdrawn claim (arXiv 2512.15035) is cited. I did not follow external links over the network.

## 4. Contribution conditions and boundary

Every condition in §6 of the frozen contribution review is implemented:

1. **Bryant–Kovács.** BK is credited in the abstract and §1. Lemma (iii) is cited at (3.4). $P_m$ is shown equal to the coordinate functional of $(e_\beta,e_{b_0},e_\beta)$ with a proof on all triples. The alphabet and content projection are presented as "a convenient expression for that classical product mechanism", not as a new mechanism. The field-injectivity limit is stated explicitly.
2. **Headline.** The title, abstract, Theorem 1 and §1 lead with the integral and every-ring regular summand. The char-2 multiplicities and odd $p\le2m-1$ are named. The generator and functional are called "devices".
3. **Optional remarks.** These are correctly neither assumed nor added. The deficit and palette proof is kept in full.
4. **Context.** The stipulated complex Saxl theorem is described as context and is not used. The credits to Ikenmeyer, the pinned deficit and factorial, I21 together with HR (complex regular containment), and HR (char-2 PIM occurrence) are all present. Not new are disclaimed. There is no worldwide-priority claim.

The brief's specific interfaces also hold: BK's Lemma (ii)/(iii) field injectivity is not transferred to $\mathbb Z$, Ikenmeyer's uniqueness is credited, the pinned deficit and factorial scalar are credited, and the complex regular and char-2 PIM results are marked as already known.

**Duplicate evidence.** I did not repeat the contribution search. Two targeted web searches ("staircase Specht module tensor cube regular module direct summand positive characteristic"; "Saxl conjecture modular tensor cube free summand group algebra symmetric group integral 2025 2026") returned nothing that states a free or regular summand of a staircase Specht tensor power over $\mathbb Z$ or in positive characteristic. The withdrawn 2512.15035 appeared and is irrelevant. **No new duplicate evidence was found.** This is a bounded check, not a priority claim. The narrow SUBSTANTIAL verdict stays the contribution reviewer's.

## 5. Presentation and QA

- **Fresh typesetting.** Tectonic 0.17.0 (`/tmp/frontier-typeset/tectonic`, SHA-256 `a98aa59a…46da`) was run by the package's `build.py` on a disposable copy. The rebuilt PDF is **byte-identical** to the frozen `main.pdf`. All six rendered page PNGs and the extracted text are also byte-identical. There are 0 overfull boxes, 0 underfull boxes and 0 undefined references. pdfinfo reports 6 pages, US letter, and the correct title and author metadata. All fonts are embedded.
- **Visual check.** I inspected all six pages at 120 dpi. There are no overflows, clipped displays, broken references or orphaned headings. Equations (3.1)–(3.4) and (4.1)–(4.2) are numbered, and the bibliography fits on page 6. Layout is clean.
- **Text extraction.** In the pdftotext output, $\ne$ appears as `6=` and some math glyphs have no Unicode mapping, because the LM math fonts carry no ToUnicode entries. This affects accessibility and search only (O9).
- **Public ZIP.** The ZIP has 32 members: the 31 allowlisted payload files plus `public-manifest.json`. It contains no `inputs/` path, no third-party reading copy and no I21 file, and it was verified by the package verifier on the copy.

## 6. Final-package conditions (not repairs of the frozen paper)

**F1. Formal-coverage integration.** The paper says "No full Lean formalization is supplied or claimed" and that the formal-coverage status accompanies the source. Both remain true only while `formal-scope.json` is an honest placeholder. Before final release, the parent's separate supplement must state the actual coverage of `staircase-formal-v1`. That coverage is the abstract conditional split, equivariance and complement results under the hypothesis `Separates`, base change of split maps without flatness, and the integer zero-deficit implication. The supplement must also list what is **not** formalized: the Specht lattice and polytabloid identification, the palette lemma, the square budget and row moments, the staircase instance of `Separates` (that is, Proposition 3 and (3.4)), the equivalence (3.3) with $J^{-1}\pi q^B$, the sign $+1$, and the multiplicity statements. It must not describe the independent semantic review as passed unless it has passed. A separate supplement keeps this paper valid as written. No sentence of the frozen paper conflicts with that plan.

**F2. Access to I21.** The paper cites "I21 §2.1" with a specific content claim, and the draft ZIP gives readers only a SHA-256. A final public package must make the cited note resolvable. Either include the author-owned original note with its rights notice, so that its hash can be verified, or provide a stable public link to the identical bytes. An excerpt alone would not verify against the cited full-file hash. This is a citation-access condition, not a mathematical one. The integral proof does not use I21, and §3 above shows the antecedent can also be checked from public sources. The note contains internal relative links and unrelated negative results; the parent should keep them unchanged, or add a cover note explaining them, rather than edit the hashed bytes.

## 7. Optional clarifications (none required)

- **O1.** In §5, "The pinned source stipulates …" should read "proves; this note accepts it as stipulated". The next sentence already says this.
- **O2.** In §5, also cite the public route to complex regular containment: `dom:permutation-quotient` plus HR Thm 2.4 and semisimplicity, with I21 adding the isomorphism.
- **O3.** In §1, change "supplies these multiplicities" to "at least these multiplicities". Optionally note that every field is a splitting field for $S_N$, and that $k\otimes S^\rho_{\mathbb Z}$ is James's field Specht module (standard basis theorem). This would make the HR char-2 comparison literal.
- **O4.** In §1, give a citation for $f^\rho=N!/\prod h$ and for the divisibility of projective dimensions by $|G|_p$.
- **O5.** In §3, (3.4) is introduced with "consequently" before Proposition 3 proves it. Say "together with Proposition 3".
- **O6.** The letter $D$ is overloaded: simple modules (§1), ordered block (§2) and $\mathcal D$ (§3). $e_a$ denotes both words and local letters in (3.1).
- **O7.** Define $z_{m,A}=1\otimes z_m$ in Theorem 1.
- **O8.** State that the Ikenmeyer section and equation locators refer to arXiv v2.
- **O9.** Add ToUnicode or cmap support for math glyphs to improve PDF text extraction.
- **O10.** State $ge_t=e_{gt}$ explicitly in §2.

## 8. Independent checks and reproducibility

All runs used Python 3.14.7 with assertions enabled, from this directory:

```sh
python3 -B audit_inputs.py        > input-manifest.json      # 38 inputs, 8 brief hashes: PASS
python3 -B independent_controls.py > independent-controls.json  # C1-C9: PASS (about 3 s)
python3 -B copy_checks.py         > copy-checks.json         # package scripts on a temp copy: PASS
python3 -B make_output_manifest.py > output-manifest.json
```

Before these scripts existed, the same package commands were run by hand on the copy `/tmp/smr1-copy-l3dv/pkg`. That copy was created with `cp -a` from a pre-run SHA-256 snapshot of all 81 files: `verify_package.py --with-inputs`, `--audit-inputs-only`, `reproduce.py`, and `build.py --tectonic /tmp/frontier-typeset/tectonic`. All passed with identical results. The pages were also rendered at 120 dpi there for the visual check.

**`copy_checks.py`** hashes the original package, copies it to a temporary directory, and runs the package's verifier (41 inputs, 13 slices, public ZIP allowlist, all manifests), `reproduce.py` (both copied controls byte-identical to their expected outputs, plus 3,072 interface comparisons) and `build.py`. It then compares the PDF, pages and text, deletes the copy, and asserts that the original is unchanged. These are reproductions of earlier controls, not new premises.

**`independent_controls.py`** was written from the paper's text only, and imports no package, candidate or review code:

| Control | What it checks | Result |
|---|---|---|
| C1 | Polytabloids built by column-group action on tabloids of $t_R$ and $t_C$ equal the literal `alt` vectors. Columns equal $R_i$ and $C_j$. Transpose scalar is $+1$. Content is $\rho$. ($m\le4$) | PASS |
| C2 | Full vector $\pi_{\mathcal D}q^B(z_m)=+e_w$: literal triple expansion for $m\le3$; for $m=4,5$, $a=c$ filtered, since $q$ kills $a\ne c$ | PASS ($m\le5$) |
| C3 | Whole matrix $P_mI_m=\mathrm{id}$ at $m=3$ under both formulas: 720 translates of 1,728 triples each | PASS |
| C4 | (3.3) against $J^{-1}\pi q^B$ on individual triples, including zero outputs. $m=2$: all 512. $m=3$: all 531,441 triples with $a=c$, plus 100,000 random. $m=4$: 140,000 targeted and random. Uses an orbit table and a separate solver. | PASS, 0 mismatches |
| C5 | Palette lemma by exhaustive backtracking | Unique solution $\beta$ for $m\le8$ |
| C6 | Deficit step: every row-palette pair whose output first coordinates have content $\{r^r\}$ has $d\equiv r$ on each row | Exhaustive, $m\le6$ |
| C7 | Hook list, $f^\rho$, and $v_p$ divisibility | Non-projective exactly at odd $p\le2m-1$, for $m\le15$ |
| C8 | Complex antecedent: rank of $G(v_R\otimes v_R)$ equals $\dim M^\rho$; pair-letter scalar $(-1)^H\prod r!$ | $m\le3$ |
| C9 | Mutations at $m=2,3$: $v_R^{\otimes3}$ gives 2 and 12 words with coefficients $\pm1$; dropping the $a=c$ filter gives $0$; reversing only the top-row order gives $-1$; $v_C\otimes v_R\otimes v_R$ gives $+e_w$ at the identity. That case is a symmetry, not a mutation: layers 1 and 3 enter only through $a=c$. | Mutations detected; symmetry confirmed |

These finite checks support the review. They do not prove the all-$m$ theorem, which rests on the reconstruction in §2.

**Frozen inputs unchanged.** I took SHA-256 snapshots of all 81 files of `staircase-manuscript/` before any run and compared them after all runs, and checked the brief hashes again (§1). They are identical. `copy_checks.py` asserts the same thing internally. Package scripts ran only on temporary copies.

## 9. Outputs

`review.md`, `independent_controls.py`, `independent-controls.json`, `copy_checks.py`, `copy-checks.json`, `audit_inputs.py`, `input-manifest.json`, `make_output_manifest.py`, `output-manifest.json`. The output manifest lists the bytes and SHA-256 of every other file in this directory.
