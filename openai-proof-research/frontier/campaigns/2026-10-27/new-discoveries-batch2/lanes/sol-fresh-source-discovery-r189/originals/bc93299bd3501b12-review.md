# T238B125 — independent contribution review, round 1 (Factory Opus fallback)

**Decision: TECHNICAL** (conditional on correctness; correctness is NOT reviewed here).

The complete frozen theorem is a genuine, stronger, new-to-project statement: bounded-bias, fully nonhomogeneous, time-inhomogeneous Thorp sweeps on $N=2^d$ cards mix the full deck in $O_\delta(d^2+d\log(1/\varepsilon))$ physical steps, which is sharp in order by the credited r113 lower bound. It is not REDISCOVERED in project history or in the external primaries read. But after the stipulated source238 contracts are used as stated, the integrated upper deduction leaves no substantive unpaid compatibility operation. Every interface between the ingredients matches as stated, and the one non-classical step is a re-aim of the source's own placement-fiber disintegration. No acceptance, count, gate or worldwide-priority statement is made.

This review was written by an independent reviewer. It is not the failed prior task and does not reuse any of that task's output. The output directory did not exist before this round, so no partial files had to be treated as unreviewed. No nested agents, author or shared-index edits, git mutations, publication, contacts, or formal or manuscript work occurred.

---

## 1. Sealed inputs and read-only controls

Detached anchors were supplied by the parent. I recomputed them on the live author tree, and all four match:

| Object | SHA256 |
|---|---|
| `fresh-structural-discovery-r125/FINAL.json` | `b177b36d6ef39750a4621d0fd1f4c73a5d4891c74fc0cd6d9041b0d5eb7aa41e` |
| `fresh-structural-discovery-r125/REPORT.md` | `b89f5d434fca85f54757202e50959546c6224f8ac7beadac3d75cd64dfb4cee4` |
| `packet/MANIFEST.json` | `4c6aaaa4b6c31dccd03ca58677bd3279f6de0646f3366e7341493d32b20de6cc` |
| `copied-controls/receipt.json` | `d611270809d28962ac8a66b4636a2b2565546d99994cce6292c581a12a1ef454` |
| `packet/public/FROZEN-SCOPE.md` | `ec09396badbea0351a0eb2f8bdb7b780e1d74ffdace92bb04114cccdc5be4a22` |
| `packet/public/proof.md` | `fc725dd2d70ca3a5a52bcfdca7da954e674a3157353b831dd2caf6badd097881` |

The author's `verify.py` installs an audit hook that denies writes, subprocesses and sockets. With the detached FINAL and REPORT hashes it returned `ARTIFACTS_AUTHENTICATED_ONLY` (110 payload files, 39 canonical records, 19 retained sources, 5 primary pairs, 1 failed request, both gates false).

My own copied-artifact controls ran on a disposable copy in `/tmp`, which was removed afterward:

- The baseline was accepted.
- A wrong detached FINAL hash was rejected.
- A one-byte change to `proof.md` was rejected as a payload mismatch.
- A one-byte change to the outside `REPORT.md` was rejected.
- The restored baseline was accepted.
- `finite_disintegration.py` stdout equals the stored `finite-disintegration.json`.

The author-tree fingerprint (SHA256 of the sorted per-file hash list) was `61ee0ad0…bddcafb` both before and after. The full transcript is in `controls-transcript.txt`.

These checks authenticate bytes only. They are not mathematical or contribution gates.

## 2. Exact object reviewed

The object is FROZEN-SCOPE.md (bytes above), with its whole integrated upper deduction in proof.md §§1–8 and the credited r113 lower bound in §9. Stated briefly: for $0<\delta<1/2$ there is $C_\delta$ such that, for every $d\ge1$, every deterministic array $p_{t,x}\in[\delta,1-\delta]$ of independent switch probabilities, every initial deck, every $\varepsilon\in(0,1/4]$ and every $t\ge d\lceil C_\delta(d+\log(1/\varepsilon))\rceil$, the full-permutation TV distance is at most $\varepsilon$. No homogeneity, periodicity or common eigenbasis is assumed. The scope requires the full theorem, not a variant, and I reviewed it at that scope.

## 3. The integrated deduction, step by step, against what is already paid

The table compares the deduction against operations actually read in the pinned source (`Conditional-coordinate-sweeps-and-analytic-transfer-September-26-2026`, hereafter S238C; local retained bodies are byte-checked by the verifier against pinned Git blobs).

| proof.md step | Operation | Where it is already paid |
|---|---|---|
| §1, eq. (1) | $\Vert K^{\mathcal H}_\mu\Vert_{op}\le D_\mu^{-a}n^{bh}$ at $z=0$ | Direct reading of S238C `03-paths.tex` `thm:conditional`/`ac:main`, `ac:eq:15` (every feasible $\mathcal H$, $c(s)\ge c_0$, $e(s)\le e_0$, $C(\mathcal H)\ge0$). |
| §2, eq. (2)–(3) | Lift a conditional residual operator to $[\lambda]$ of $S_n$ with $D_\lambda\le(n)_hD_\mu$ for every constituent | Same operation as S238C `06-induction.tex` §"Adding the cells outside the hook" (`ac:part:245`, `ac:eq:22`): the induced representation from placements of $k$ cards, Frobenius reciprocity, $F(\lambda)\le F(\gamma)+k\log s$. The source realizes full averages as fibers whose blocks are $p_{\mathcal H}(x,y)$ times the conditional operator with augmented paths. |
| §3 | Disintegrate a network whose lines in $F$ carry arbitrary laws $Q_L$: reveal all occupants of $F$'s slots with full paths; record atom = path cylinder; RN derivative constant on atoms; mixture of source conditional laws; $h\le R^2k$ | The cylinder identity is immediate: each slot of each line is occupied by exactly one card, so "all cards through $F$" is a deterministic function of their (endpoint-determined) paths, and injectivity gives the converse. The RN step is elementary (the record fixes every $g_L$, $L\in F$). The cost $e_0h\log n$ is the term `ac:eq:15` already carries so that paths can be revealed (S238C intro §"The conditional estimate": "The correction is the invariant that permits more paths to be revealed"). The disintegration of a full average into source-conditioned fibers is the engine of `ac:part:245`. **What is new is only the aim:** using the every-$\mathcal H$ contract as an external change-of-measure device for arbitrary laws on a few lines. |
| §4 | Bernoulli($z$) line replacement; $(1-z+zn^B)^{L}$; segment $[\eta_n,2\eta_n]$ with $\eta_n\asymp n^{-B-2}$; $D_\lambda\ge n/e$ off trivial and sign | Elementary arithmetic. The dimension inputs are S238C `02-preliminaries.tex` (`ac:eq:1` and the large-$k$ bound). |
| §5 | Disk $\vert z\vert\le r_\delta>1$ for $(1-z)P+zQ$ with $Q$ a product of $(1-p)I+p\rho(\tau)$ | S238C `07-analytic.tex`, verbatim structure. "Product of orthogonal projections" becomes "product of strict contractions off the fixed line"; the norm-attaining argument and the $PQ=QP=P$ block decomposition are unchanged. Uniformity over $[\delta,1-\delta]^J$ is a compactness remark. |
| §6 | Transfer from the shrinking segment to $z=1$ with loss $1/\log n$ via a normalized disk Green potential | The structure is S238C `07-analytic.tex` (subharmonic $\log\vert f\vert+AG$, boundary maximum principle). Replacing the free logarithmic barrier by the disk Green kernel, so that $W(1)\gtrsim1/\log(1/\eta)$, is the classical harmonic-measure (two-constants) estimate for a short segment. It is a routine correction, which the author does not claim as new. |
| §7 | Fourier sum, sign block, nonidentical sweep products | S238C `07-analytic.tex` Diaconis–Shahshahani sum, with $gw$ replaced by $\gamma_\delta s/\log n$. Time inhomogeneity costs nothing because (9) is uniform in all probabilities (submultiplicativity). The sign term $\prod(1-2p)$ is elementary. |
| §8 | Small $d$ by uniform minorization; later times by TV contraction | Routine. |
| §9 | Homogeneous $\Omega_p(d^2)$ lower bound | Credited verbatim to structural r113 `screen-238.md`. Not a contribution. |

## 4. Independent tests: is there an unpaid compatibility operation?

I did not decide this by listing ingredients. I tested where the integration could have needed a new idea.

**(T1) Can the source theorem be applied directly at a fixed small $z>0$ with biased lines?** No. In the standard representation $[n-1,1]$, the character $\chi(x)=(-1)^{x_1}$ of the first bit is killed by $U$ on each stage-1 line, but $B^{(p)}$ multiplies it by $1-2p$. Later stages do not touch bit 1. So $\Vert K_{[n-1,1]}(z)\Vert\ge z\vert1-2p\vert$, a constant, while any `ac:eq:15`-type bound demands $\le(n-1)^{-a}\to0$. The fair source's fixed-segment route is therefore unavailable. This is r113's obstruction seen at the operator level, and the author states it correctly. The question is then whether getting around it requires a new mechanism.

**(T2) Is the disintegration really needed, or does a cruder bound suffice?** A cruder bound does not suffice. Bounding altered-line terms by $\Vert K_F\Vert\le1$ gives $\Vert K(z)\Vert\le D_\lambda^{-a}+Lz$. Keeping a dimension power then forces $z\lesssim n^{-2}D_\lambda^{-a/2}$. For $\log D_\lambda\asymp n$ the transferred exponent becomes $O(1)$ rather than $\gamma\log D_\lambda/\log n$, and the Fourier sum then needs about $n\log n$ sweeps. So keeping $D_\lambda^{-a}$ multiplicatively on every altered-line term is essential, and that is exactly what §3 supplies.

However, once one wants that, the every-$\mathcal H$ quantifier in `ac:eq:15` offers precisely one natural route. Condition on the paths covering the altered lines, pay $n^{(a+b)h}$ through `ac:eq:22`-style branching, and note that the likelihood ratio is measurable with respect to that record. No hypothesis mismatch has to be repaired:

- The source theorem allows any feasible $\mathcal H$, including families sharing lines.
- It needs no independence between $\mathcal H$ and the network, because it is a statement about each fixed cylinder.
- It needs no density bound on $Q_L$, because the $Q_L$ enter only through mixture weights.

**(T3) Is the segment-length versus cost trade-off delicate?** No. The cost per altered line is $n^{O(1)}$, there are at most $n^2$ lines, so a polynomially short segment keeps a fixed fraction of the exponent. Harmonic measure of a segment of length $\eta$ seen from distance about 1 is about $1/\log(1/\eta)$, which gives $1/\log n$. The match with the $d^2$ lower bound is a consequence of these two numbers, not an extra mechanism. prefreeze.md shows all three facts (the per-line cost, the polynomial segment, and the Green-potential correction) already worked out as feasibility sketches before the freeze, which is consistent with a short routine derivation. That timing is disclosed and is not held against the author.

**(T4) Do the stronger fair-specific companion contracts already give it?** They do not, which supports "not REDISCOVERED" but not substantiality.

- *Compatibility entropy* `tra:duality:weighted` (introduction, read) does accept arbitrary nonnegative row and column weights. But `tra:duality:moment` asserts $Z_n(p_*)\le1+1/16$ for the fair sweep. For a homogeneous biased sweep, the one-card operator flips each bit with probability $p$, so $[n-1,1]$ has $d$ singular values $\vert1-2p\vert$, and $Z_n(p)\ge(n-1)\,d\,\vert1-2p\vert^{2p}\to\infty$. The bounded regular moment, and hence that route's conclusion, is false for biased sweeps. Its sparse estimate also uses a fair-swap occupied-set inequality, as the introduction states. The weighted inequality alone is a middle-grid lemma, not a biased-sweep theorem.
- *Optimal-order mixing* (as reported in r113 and I132) uses exact annihilation by fair coordinate averages and uniform one-card marginals. Both fail for biased switches.

**(T5) Refined deterministic-scan transfers from external primaries.** These are spectral-gap or Dirichlet-form transfers, so they produce bounds that are uniform in $\lambda$ or comparisons between reversible chains. The theorem needs a dimension-power contraction $\Vert K_\lambda\Vert\le D_\lambda^{-\gamma/\log n}$ for a *nonreversible deterministic biased scan*. My own refinement of the telescope used stage-level operators: the $d$ stage averages, which are commuting products within a stage and are projections in the fair case. Gaitonde–Mossel Cor. 3.1 (or its extension to strict contractions) then gives at best $\Vert K_\lambda\Vert^2\le1-\delta_\lambda/(8(d+1))$ with $\delta_\lambda\le1$. This forces $s\gtrsim d\log D_\lambda$, which is about $d\,n\log n$ for top representations.

Comparison through Hermon–Salez Thm 2 / Lemma 3 (Dirichlet form of the cube interchange $\asymp|V|^{-1}$ times that of the complete graph) is eigenvalue-by-eigenvalue only for reversible random-update chains. Jonasson Lemma 2.1 is likewise an $L^2$ comparison between symmetric random-edge chains with loss $A^*$. I know of no transfer that turns either into per-$\lambda$ dimension-power bounds for the ordered biased scan. So no external route found here pays the theorem. As instructed, that failure does not establish substantiality.

**Conclusion of the tests.** The theorem is stronger than anything read, but its proof is: the source's conditional contract used with its own placement-fiber disintegration, followed by the source's analytic transfer with a classical harmonic-measure normalization and a polynomially short segment. Each interface matches as stated. I found no step where two stipulated or classical inputs fail to fit and a new estimate, construction or invariant has to be supplied. Under the campaign rule that conditional expectation, induction and classical transfer alone are not new, and that a full stronger theorem can still be TECHNICAL, the integrated contribution is **TECHNICAL**.

What would change this verdict:

- **To SUBSTANTIAL:** a correctness review finds that the §3 lift or cylinder step actually requires an estimate beyond `ac:eq:15`/`ac:eq:22` (for example, if a constituent bound needed more than the stated every-$\mathcal H$ contract), and the author supplies that estimate.
- **To REDISCOVERED:** an unread source238 companion, or Morris's pairwise-condition framework (0802.0339) or Czumaj (STOC 2015), already states an arbitrary-bias version.

## 5. Antecedents compared (actual bodies)

- **Structural r113 `screen-238.md`** (read in full from the author's private copy): the exact lower calculation $\mathbb E F_s=N\rho^s$, $\operatorname{Var}\le2N$, $\operatorname{Var}_U=N^2/(N-1)$ gives $\Omega_p(d^2)$. Its "failed linear biased upper scale" is the observation that the fair $O(d)$ scale cannot persist. r113 freezes no target and proves no upper bound. The lower bound is credited and is not part of this verdict.
- **Structural r122 `other-screens.md` §238** (read): repeats the r113 exclusion and makes no claim about the optimal biased rate.
- **I132 Candidate T** (author's private copy, lines 65–75 read): exact path cylinders, revealed-environment preparation, active and reset operations, arbitrary multiplicities, and the averaged remaining-half law in the *revealed switching environment* companion, all for fair switches. This makes "exact coin/path cylinder plus conditional law" a project-familiar pattern. It does not contain a biased upper theorem, and it explicitly notes that companion conclusions are not uniform over every fixed rare environment. The author's step avoids that limitation by using the every-$\mathcal H$ theorem rather than averaged results, which the author states correctly.
- **I135 §2.4** (grep-located and read): the $X,\,Y=X^{-1}$ dependence obstruction and the parity obstruction. These are irrelevant to §3 because the mixture there is over exact cylinders of one network with a constant likelihood ratio, not a product of dependent marginally uniform laws.
- **Project-wide search** (bounded `rg` over `frontier/` and `proposals/` for Thorp and biased, inhomogeneous or arbitrary-probability terms near shuffle, sweep or switch, excluding CONTENTS copies and r125 itself): this found only r113, r122, r114's copy of r113, the briefs, and the separate `t238b125-proof-r1` directory. I did not read that directory's verdict, to keep this review independent. No earlier biased upper bound exists in the project. The result is new-to-project.

## 6. External primaries (author-retained bytes; hashes in its private register)

- **Jiang 2610.18884v1** (`jiang.txt` lines 120–190 read): Theorem 1.1 gives fair Thorp $t_{mix}\le C_*d^{5/3}+O(d^{4/3}\log d)$, with fair coins in the model (1.4)–(1.6). It is weaker than the source and has no biased statement in the part read.
- **Gaitonde–Mossel 2410.11136v2** (lines 755–805 read): Theorem 3.1 and Corollary 3.1 for orthogonal projections, $\Vert P_n\cdots P_1\Vert\le1-\delta/(8(n+1))$. My assessment of the refined transfer is in (T5).
- **Jonasson 1210.6916v1** (Lemma 2.1 and the proof of Prop. 1.1 read): $L^2$ comparison with loss $A^*$ for symmetric random-edge chains. The v2 request returned 404, as recorded by the author.
- **Hermon–Salez 1905.02146v2** (statements of Theorem 2 and Corollary 2 at lines 256–285, and the location of Lemma 3 at line 661): $\chi^{ip}_G\asymp|V_G|$ for product graphs, giving continuous-time $O(\log N)$ interchange mixing on the cube. I did not re-read the octopus proof; the author's reading is noted, not relied upon.
- **Web navigation (two searches):** found Morris (math/0507307, 0802.0339, 0912.2759), Jiang, and Czumaj/Czumaj–Vöcking switching networks. None of them was read beyond search snippets, and every snippet describes fair coins. This is navigation only, not a priority clearance.

## 7. Reading limits

S238C retained bodies, read in full: `03-paths.tex` and `07-analytic.tex`. Read in part: `01-introduction.tex` (lines 1–30 and 140–230), `06-induction.tex` (`ac:part:245`, lines 300–345), and the branching lines of `02-preliminaries.tex` that I located. Compatibility-entropy `00-introduction.tex` was read through the theorem statements, the first-proof outline and the methodological context; `03-spectral-conversion.tex` was not read. The remaining sections of S238C (sparse, density, the rest of the induction) and the other ten Thorp companions were not read beyond CONTENTS.md entries 5838–5946, all of which describe fair shuffles. I did not truth-audit any upstream statement; all pinned statements and operative proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. External primaries are not stipulated and were not checked for correctness. I did not read the author's private search records beyond the history bodies cited in §5.

## 8. Separation

- Correctness of proof.md, in particular the §2–§3 constituent and cylinder steps and the §6 constants, needs the separate correctness review. This verdict is explicitly conditional on correctness.
- This review assigns no acceptance, count or gate, starts no downstream work, and makes no claim about worldwide priority.
- Author bytes were preserved; the fingerprint was unchanged before and after.
- Private sources, primaries and history bodies were used for local review only under their original rights. This review quotes only short identifiers and labels and must stay under the same private/public separation.
- This round wrote only `t238b125-contribution-r1/`: `review.md`, `controls-transcript.txt` and `SEAL.json`. The SHA256 of SEAL.json is reported detached to the parent.
