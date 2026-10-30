# Contribution / prior-work audit r1 — full FK/Pareto-resistance theorem F

Reviewer role: independent contribution sub-agent (Opus 5.5, normal mode), round 1.
Author of the reviewed candidate: Myeongjin Kang, no affiliation.
This review: original prose CC BY 4.0. Private third-party materials retain their rights.
Date: 2026-10-16. Directory: `fk-frechet-contribution-r1/` only.

## 0. Verdict

**TECHNICAL** for the entire original scope of F.

F is not a duplicate of any statement I found. But every operation in the
proposed bridge reduces, by routine substitution, to a named primary result or
to an elementary operation that an expert would supply in a paragraph:

1. The finite-second-moment fringe law of large numbers, including the
   "near-conditioning-size" control, is Janson's Remark 5.3
   (arXiv:1312.1211v1). Its hypothesis is $|\mathbb E f(\mathcal T_k)| = o(k^{1/2})$.
   For the bridge toll this holds trivially, because $f \le |T|^\alpha$ and $\alpha<1/2$.
   For the weighted-child toll it is a ten-line check (Section 4 below). That
   check uses only the Otter–Dwass forest formula, the finite-variance local
   limit theorem, and Chebyshev's inequality.
2. The Fréchet law is the elementary conditional product of independent
   Pareto tails once that law of large numbers holds.
3. The spectral identification is the classical cut-vertex (series)
   decomposition of the Green operator, the classical tree bridge term
   $R_e\,u_e\otimes u_e$, and a standard dominant-rank-one / Gram perturbation
   with a small-trace remainder.
4. Cyclic-block negligibility uses one idea: an edge cut of size at least two
   doubles the Pareto tail exponent. Here that follows from Menger's theorem and
   the independence of two edge-disjoint path sums. This is the standard trap
   mechanism (a trap needs every edge of a cut to be bad) that Flegel credits
   and uses. The resulting $\alpha$-moment, linear in block size, is then fed
   back into Janson's Remark 5.3.

The q>4 input enters only through the pinned source's exact decorated
Galton–Watson representation and its finite offspring variance. The same proof
works verbatim for any block-decorated critical finite-variance
Galton–Watson map family. That is a sign of substitution, not of a q>4-specific
bridge.

What remains unpaid by the literature is real but small: the specific
assembly, and one short hypothesis check. That is a publishable *technical*
corollary-level result. It is not a substantial bridge by the campaign standard
("complete nonroutine theorem; no inflated count for technical corollaries").

This is **not** a proof PASS. I did not audit the proof for correctness beyond
what the contribution assessment needs (Section 7 lists items I noticed in
passing, all non-binding). I did not read the parallel proof audit
`fk-frechet-proof-r1/`, to keep this review independent. **No worldwide
novelty or priority certificate is given or implied.**

## 1. Exact scope assessed (unchanged)

The verdict applies to F exactly as fixed in `original-scope.md` and
`candidate.md` §1 (lines 12–55):

* Every fixed real $q>4$ and every $\alpha\in(0,1/2)$.
* For each integer $n\ge1$, the rooted spherical $n$-edge FK map with weight
  $q^{k_M(A)+(|A|-|V(M)|)/2}$. Loops and parallel edges are retained.
* Independent resistances on **every** edge with $P(R>r)=r^{-\alpha}$, $r\ge1$.
* Speed measure $m(v)=\deg_M(v)$, counting both darts of a loop, so $\sum m=2n$.
  Energy sums over non-loop edges with multiplicity.
* $\tau_n=\sup \mathrm{Var}_m(f)/\mathcal E(f)$, with $\tau_n=0$ on a one-vertex map.
* $K(q,\alpha)=p_2\,\mathbb E|T|^\alpha$, where $(p_k)$ is the exact
  `block:offspring` law and $T$ is the unconditioned GW tree.
* $P(n^{-1/\alpha}\tau_n\le x)\to\exp(-Kx^{-\alpha})$ for every $x>0$, through
  all integers $n$.
* Only the finite second offspring moment is available. There is no third
  moment, no bounded blocks, no tree-only or bridge-only disorder, no changed
  clock, no subsequence, and no reduced alpha range.

No narrowing was used anywhere in this assessment. The TECHNICAL verdict is
about this full statement, not about a sub-case.

## 2. Authentication and frozen inventories

I ran an independent hash-only authentication. It was an inline Python script
that reads bytes only. **No stored candidate code (`verify.py`, `checks.py`)
was executed.**

| Item | Result |
|---|---|
| `seal.json` SHA256 | `80f72efab2af1c25bb440a49fcaacd5410601d328b83c0f59055be65958ae7bc`, matches external seal |
| `seal.sha256` | matches `<hash>  seal.json\n` |
| `inputs-manifest.json` | 7741 bytes, SHA256 `f077a3bb…a8ba8`, matches seal; 34 files |
| `outputs-manifest.json` | 2751 bytes, SHA256 `43890b32…71857`, matches seal; 18 files |
| All 52 inventoried files | size and SHA256 match |
| Membership | exact: no extra files besides seal/manifests; no symlinks |
| Pinned upstream blobs | 13/13 Git-blob SHA1 match `preprints-tree.json`; all URLs contain `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| `candidate.md` | 24061 bytes, SHA256 `1b0e0608be24cb8f484f71643b1f488dace849509d4f21d442110bbb09750768` |

The frozen candidate directory was not modified. The parent's checker replay
receipt was not re-run. It is finite support only and plays no role in a
contribution verdict.

Reviewer-side files (this directory only): `status.json`, `progress.md`,
`review.md`, `reviewer-sources.json`, and `literature/fill-janson-2104.02715v1.{pdf,txt}`.
The PDF was first downloaded to `/tmp/fkc`. It was then moved here, and the
empty temporary directory was removed. SHA256 values are in `reviewer-sources.json`.

## 3. Reading extents

Frozen candidate package (read in full unless noted): `candidate.md`,
`original-scope.md`, `literature-screen.md`, `source-contracts.md`,
`working-math.md`, `review-brief.md`, `seal.json`, `verify.py`. I did not read
`checks.py` in full, because it is support only.

Pinned source (*Brownian CRT limits of finite FK maps above four*, frozen
copies, blob-authenticated):

* `main.tex` lines 35–110: `eq:finite-law`, `eq:degree-measure`, `thm:main`.
* `sections/blocks.tex` in full: `block:decomposition`, `block:critical`,
  `block:offspring`, `block:moments`, `block:finite-law`. Note that the source
  itself credits Tutte, Addario-Berry 2019 and **Stufler's enriched-tree
  framework** for the decomposition.
* `sections/trees.tex` lines 1–140: `tree:assumptions` (marks with law
  $\mathcal L_k$, finite variance), `tree:excursion`, `tree:maxdegree`, and
  `tree:conditioning` (Otter–Dwass and the finite-variance local limit).
* `sections/metric.tex` lines 85–134: `metric:measure` (corner mass equals the
  degree measure exactly).
* `references.tex` in full.

Primary antecedents:

* Janson, arXiv:1312.1211v1 (frozen copy). Lines 100–330: Theorems 1.3 and 1.5,
  Remarks 1.4–1.12. Lines 600–1000: Lemma 4.1, (4.7) cyclic representation,
  (4.12)–(4.13), Lemmas 5.1–5.2, proof of Theorem 1.5(i), Remark 5.3, Lemma 5.4.
* Fill & Janson, arXiv:2104.02715v1, *The sum of powers of subtree sizes for
  conditioned Galton–Watson trees* (fetched by me). Lines 80–340: Theorems 1.1,
  1.2, 1.6, 1.7, 1.10, 1.12 and Remarks 1.13–1.14.
* Flegel, arXiv:1608.02415v3 (frozen copy): abstract and contents (lines 1–50).
  I relied on the candidate's cited locations for Theorem 1.8 and
  Corollaries 1.10–1.11. I did not re-read the proof sections.
* Faggionato, EJP 17 (2012) paper 15 (frozen copy): lines 540–589,
  Theorem 2.5 (random barrier model; eigenvalue scale $n^{1+1/\alpha}$;
  generalized differential operator limit).
* Feng, PTRF 2026 (frozen copy): grep of Remark 1.7 (lines 216–250); not re-read in full.
* Web screen, abstract or title level only: Collevecchio–Jung arXiv:1702.04087
  (mean-field random conductance spectrum); Yang arXiv:2408.07139 (gap of
  random conductance model on a segment); Gantert–Müller–Popov–Vachkovskaia
  (random walk on supercritical GW trees with random conductances); and
  heavy-tailed random matrix extremes (Soshnikov; Auffinger–Ben Arous–Péché,
  AIHP 2009 "Poisson convergence for the largest eigenvalues of heavy tailed
  random matrices"). I also checked Astrauskas' extremal spectral theory for
  Anderson Hamiltonians by title. I read none of their proof bodies.

Discovery history: `strict-bv-parent/fresh-r7-brief.txt` (1389 lines, SHA256
`8432ecdc…08ae`), targeted reading of the campaign's standards and vetoes only.

## 4. Operation-level reduction

### 4.1 Table

| Candidate step | Lines | Primary operation that pays it | Residual new work | Class |
|---|---|---|---|---|
| Lemma 3.1, (3.1)–(3.5): integrable-toll LLN with near-$N$ control | 101–170 | Janson 1312.1211 **Remark 5.3**: $\mathbb E\lvert f(T)\rvert<\infty$ and $\lvert\mathbb E f(\mathcal T_k)\rvert=o(k^{1/2})$ give annealed **and** quenched LLN. By (4.13), $\mathbb E f(\mathcal T_k)=h_k/\pi_k$ with $\pi_k\asymp k^{-3/2}$, so (3.1) $h_s=o(1/s)$ **is exactly** Janson's hypothesis. (3.4) is Janson (4.7)/Lemma 5.1. (3.5) is Janson Lemma 5.2(ii). | Marks. Given the tree, marks are independent across nodes, so apply Remark 5.3 to the unmarked conditional-mean toll and finish with conditional Markov/Chebyshev. Routine. The candidate itself credits Janson (lines 97–99, 481–484). | Known |
| (3.3) expected-tail uniformity | 117–120, 155–156 | Not needed for F. The in-probability LLN for $f\mathbf 1_{f>H}$ from Remark 5.3 suffices for (5.4) and (7.1); see §4.3. | none | Known/unnecessary |
| Lemma 3.2: $\mathbb E[h;\lvert T\rvert=s]=o(1/s)$ for $h=k\sum_i\lvert T_i\rvert^\alpha$ | 172–237 | Verifies Janson's Remark 5.3 hypothesis. Tools: Otter–Dwass forest formula (Janson survey Thm 15.5, cited by the source), finite-variance local limit (Janson Lemma 4.1; source `tree:conditioning`), and a lower-deviation bound. | About 10 lines. §4.2 gives an independent version needing **only Chebyshev**, not the candidate's Chernoff bound (3.7). | Routine check |
| (6.1)–(6.2) bridge LLN $n^{-1}\sum_e s_e^\alpha\to p_2\mathbb E\lvert T\rvert^\alpha$ | 364–383 | Janson Remark 5.3 applied to $g(T)=\tfrac12\mathbf 1\{\xi_\varnothing=2\}\lvert T_{\rm opp}\rvert^\alpha$. The hypothesis holds trivially: $\lvert\mathbb E g(\mathcal T_k)\rvert\le k^\alpha=o(k^{1/2})$. The analogous all-node sum is Fill–Janson Thms 1.6–1.7(ii), 1.10(ii): $X_n(\alpha)=n\mu(\alpha)+O_P(n^{\alpha+1/2})$ for $0<\alpha<1/2$ under only $0<\mathrm{Var}\,\xi<\infty$. | Link marks are iid Bernoulli(1/2) on degree-2 nodes given the tree, with variance $\le N^\alpha\sum g=o_P(N^2)$. Exact constant from source `block:one-edge` ($b_1=2(1+\sqrt q)$, link and loop equal) and `metric:measure`. | Substitution |
| (6.3) conditional Fréchet product | 385–398 | Elementary extreme-value theory for independent Pareto variables with deterministic weights $t_e$ satisfying $\sum t_e^\alpha\sim Kn$ and $\max t_e^\alpha=o(n)$ (classical triangular-array Poisson convergence). | none | Elementary |
| (4.1)–(4.3) $K=\sum_B J_BJ_B^\ast$, trace bound by effective resistance | 239–286 | Classical: energy-orthogonal direct sum across cut vertices (series gluing of resistance forms at points, e.g. Kigami's resistance-form theory). Trace of a Green operator is the mass-weighted sum of effective resistances. | none (weighted adjoint bookkeeping only) | Classical |
| (4.5)–(4.6) bridge term $R_e u_e\otimes_m u_e$, $\lVert K_e\rVert=R_et_e$ | 287–301 | Classical tree / cut-edge Green formula. For trees, the inverse gap is within a constant factor of $\max_e R_e\,s_e(1-s_e/M)$ (Hardy-inequality characterisation on trees, Evans–Harris–Pick / Miclo). | Exact corner mass from source `metric:measure`. | Classical + source |
| Lemma 5.1 two-path gain $\mathbb E R_B(o,x)^\alpha\le C_\alpha m$ | 305–332 | Menger (2-edge-connectivity of a non-link loopless block), Thomson's principle, independence of disjoint path sums, union bound. The underlying mechanism (a cut of size $c$ multiplies the tail exponent by $c$, so traps need every cut edge to be bad) is exactly how trap thresholds arise in heavy-tailed random conductance models, e.g. Flegel's $\gamma_c=1/4$ site-trap threshold. | A half-page computation. | Elementary |
| (5.3)–(5.4) nonbridge trace $o_P(a_n)$ | 334–362 | Janson Remark 5.3 (via Lemma 3.2 check) + Markov truncation. | none | Routine |
| §7 inverse gap ≈ largest bridge weight | 400–470 | Standard "largest entries dominate" perturbation: positive sum ⇒ $\lVert K\rVert\ge W_n$; finitely many large near-orthogonal rank-ones (Gram/Gershgorin, Weyl); small part bounded by trace with $\mathbb E\le C\varepsilon^{1-\alpha}a_n$. This is the same proof architecture as Poisson extremes for heavy-tailed matrices (Soshnikov; Auffinger–Ben Arous–Péché) and Flegel's single-site localization. The candidate concedes this (lines 488–502). | Nested-pair count (7.2): one line. | Standard |

### 4.2 Independent derivation: the Janson hypothesis for $h$ needs only Chebyshev

Let $\xi$ be critical with $\sigma^2<\infty$, $Y=\xi-1$, $S_r=\sum_{i\le r}Y_i$,
and $\pi_l=P(|T|=l)\asymp l^{-3/2}$. Put $F_j$ for the total size of $j$
independent copies of $T$. The forest formula gives
$P(F_j=r)=(j/r)P(S_r=-j)$.

**Half-sum Chebyshev bound.** Split $S_r=A+B$ into two halves. On $\{S_r=-j\}$
one half is at most $-j/2$. Then
$$P(A\le -j/2,\ B=-j-A)\le P(A\le -j/2)\,\sup_z P(B=z)\le \frac{2\sigma^2 r}{j^2}\cdot\frac{C}{\sqrt r}.$$
With the uniform bound $P(S_r=z)\le C r^{-1/2}$ (Janson Lemma 4.1), this gives
$$P(S_r=-j)\le C r^{-1/2}\min(1,r/j^2),\qquad P(F_{k-1}=r)\le C\,k\,r^{-3/2}\min(1,r/k^2).$$

**Main estimate.** Exactly as in candidate (3.8),
$$\mathbb E[h;|T|=s]=\sum_k k^2p_k\sum_l l^\alpha\pi_l\,P(F_{k-1}=s-1-l).$$

*Part $l\le s/2$.* Here the residual $r\asymp s$. The contribution is at most
$$C\,\mathbb E|T|^\alpha\, s^{-3/2}\Big[\sum_{k\le\sqrt s}k^3p_k+s\sum_{k>\sqrt s}k\,p_k\Big].$$
The first sum is $o(\sqrt s)$ by dominated convergence:
$(k/\sqrt s)\,k^2p_k\mathbf 1_{k\le\sqrt s}\to0$ termwise and is bounded by $k^2p_k$.
For the second, $s\sum_{k>\sqrt s}kp_k\le\sqrt s\sum_{k>\sqrt s}k^2p_k=o(\sqrt s)$.
So this part is $o(1/s)$.

*Part $l>s/2$.* Here $l^\alpha\pi_l\le Cs^{\alpha-3/2}$, and the forest
probabilities sum to at most 1. This part is at most
$C\,\mathbb E\xi^2\,s^{\alpha-3/2}=o(1/s)$ because $\alpha<1/2$.

Hence $\mathbb E[h(\mathcal T_s)]=o(s^{1/2})$, which is Janson's Remark 5.3
condition. The derivation uses only $\mathbb E\xi^2<\infty$. It shows that the
"no third moment" feature is already inside Janson's finite-variance framework.
Janson's Lemma 5.2 is the place where he explicitly avoids the third moment
("Since we do not assume this, we have to work harder"). F adds no new
moment barrier.

### 4.3 Why (3.3) and the near-$N$ spike discussion are not an extra bridge

The candidate's lines 235–237 stress that "arbitrary integrable fringe tolls
can have spikes at conditioning sizes". That is exactly why Janson's Remark 5.3
carries the condition $|\mathbb E f(\mathcal T_k)|=o(k^{1/2})$. It is not a
new obstacle. For (5.4), the quenched LLN for $g_H:=\mathbb E[f\mathbf 1_{f>H}\mid\text{tree}]$
(Remark 5.3 applied to $g_H\le g$) plus conditional Markov gives
$P(\max_B Z_B>\delta a_n)\to$ small. The bulk sum is at most
$\delta^{1-\alpha}\sum_B Z_B^\alpha/n=O_P(\delta^{1-\alpha})$. The annealed
version of (3.3) is never needed.

### 4.4 The q>4 and "all-edge" ingredients

* **q>4.** The proof uses only these source facts: the exact conditioned
  marked GW representation (`block:finite-law`), criticality and
  $0<\sigma^2<\infty$ (`block:moments`), $p_0p_2>0$, equal link/loop weight
  (`block:one-edge`), the exact corner mass (`metric:measure`), and the size
  local limit (`tree:conditioning`). No q-dependent estimate beyond these
  appears anywhere in §§3–7. The theorem and proof transfer verbatim to any
  block-decorated critical finite-variance GW map family (cf. Stufler 2020,
  which the source cites).
* **All-edge disorder.** Disorder on cyclic edges is handled entirely by
  Lemma 5.1. Lemma 5.1 is the elementary cut-size/tail-exponent observation.
  Its "shape uniformity" comes free from Menger, with lengths $l_1+l_2\le m$.
* **Clock.** The original-degree clock enters only through the exact identity
  $s_e=|T_{i(e)}|$. That identity is a direct reading of `metric:measure`.
* **Alpha range.** $\alpha<1/2$ is exactly the integrability range of
  $|T|^\alpha$ (Janson (4.13); Fill–Janson (1.12)). In this range the sum of
  $s_e^\alpha$ is linear, so traps are microscopic (bounded mass) and a
  Fréchet law is forced. The hard regime, where macroscopic branches compete,
  is $\alpha\ge1/2$ (compare Fill–Janson Theorem 1.10(i), non-Gaussian
  excursion functionals). It is excluded from F.

### 4.5 Comparison with the requested antecedent families

* **Heavy-tailed barriers on conditioned critical GW trees / decorated trees / maps.**
  I found no paper stating F or its tree-only special case. Faggionato
  Thm 2.5 (the barrier model on a segment) is the spine analogue: masses there
  are linear in $n$, so the limit is a Krein-string spectrum, not Fréchet.
  F's tree setting is *easier* in the relevant sense, because bounded-mass
  fringe traps dominate. Feng's Remark 1.7 and the pinned walk companions
  concern ordinary (integrable) conductances, which were screened out before
  F. No antecedent pays F directly, and none is needed for a TECHNICAL verdict.
* **Low eigenvalues and inverse-gap extremes.** Flegel (lattice Dirichlet,
  single-site localization, Weibull law) and heavy-tailed matrix extremes
  (Poisson/Fréchet edge from the largest entries) supply the operation
  "isolated extreme rank-one pieces plus a small remainder". §7 is an instance.
* **Articulation-block electrical decompositions.** These are classical
  (series gluing at cut points). The candidate does not claim them.
* **Marked fringe functional LLNs under finite variance.** Janson Theorem 1.3,
  Remark 5.3 and Fill–Janson Theorems 1.6–1.10 cover this. The source's
  `tree:assumptions` already uses independent marks with law $\mathcal L_k$.
* **Localization of extreme bounded-mass traps.** Flegel's method, in which a
  trap requires all edges in a minimal cut to be extreme, and the elementary
  nested-pair count (7.2) cover this.
* **Cyclic-block resistance estimates.** Menger plus independence (elementary).
* **Credit as instructed.** Janson's integrable-toll method (Remark 5.3,
  Lemmas 5.1–5.2) and the Flegel / Faggionato spectral extremes are credited
  above as the controlling antecedents.

## 5. Objections (line-specific)

| # | Location | Severity | Objection |
|---|---|---|---|
| C1 | `candidate.md` 484–487, 512–514 | **Major (contribution claim)** | Calling Lemma 3.2 + (5.1) "the task-specific estimate" that "pays nonbridge operator tails with only the actual second offspring moment" overstates it. Lemma 3.2 only verifies Janson's Remark 5.3 hypothesis, and §4.2 shows a Chebyshev-only verification. (5.1) is an elementary two-path tail computation. Together they do not form an unpaid bridge. |
| C2 | 235–237, 117–120 | Moderate | The emphasis on near-$N$ spikes and expected-tail uniformity presents Janson's hypothesis as a new difficulty. (3.3) is not needed for F (§4.3). |
| C3 | 366–383 | Moderate | The bridge LLN (6.1) is a trivial instance of Janson's Remark 5.3 ($f\le|T|^\alpha$) and is close to Fill–Janson's Theorem 1.7(ii)/1.10(ii). Neither the candidate nor `literature-screen.md` cites Fill–Janson. |
| C4 | `literature-screen.md` item list | Minor–moderate | Missing antecedents: Fill–Janson arXiv:2104.02715 (direct $\sum|T_v|^\alpha$ asymptotics under finite variance only); Stufler 2020 enriched trees (decorated-tree fringe and local limits, cited by the source itself); Soshnikov and Auffinger–Ben Arous–Péché (extreme eigenvalues from extreme entries); Hardy-inequality spectral-gap characterisation on trees (Evans–Harris–Pick; Miclo). None changes F's truth, but they matter for the contribution statement. |
| C5 | 305–332 | Minor | The cut-size/tail-exponent mechanism behind Lemma 5.1 should be credited as standard trap reasoning, e.g. Flegel's threshold. It should not be presented as a new "shape-uniform two-path gain". |
| C6 | 497–502 | Minor | "No operation-level reduction from those lattice statements to F has been supplied by this bounded screen" is true for a single-theorem reduction. It is answered at the operation level in §4.1: the reduction is to a composite of standard operations, not to one theorem. |
| C7 | 1–55, 472–517 | Informational | The candidate's disclaimers are honest: no SUBSTANTIAL claim, no worldwide novelty claim, and principles credited. This review does not find misattribution or a hidden scope change. |

No objection here concerns the truth of F. Proof correctness is the separate
proof gate's job.

## 6. Is there a genuinely unpaid prior bridge?

The candidate's own proposed unpaid items (`review-brief.md`) are "arbitrary
FK cyclic-block negligibility plus branch-weighted spectral separation under
only the actual finite second moment".

* *Cyclic-block negligibility* = Menger + independence + Janson Remark 5.3,
  with a ten-line hypothesis check (§4.2). Paid by routine work.
* *Branch-weighted spectral separation* = classical bridge Green term + bridge
  fringe LLN (trivial Janson instance) + dominant-rank-one perturbation. Paid
  by standard operations.
* *Finite second moment only* = Janson's standing hypothesis. His Lemma 5.2
  already removes any third-moment need.

So no unpaid bridge remains that would justify SUBSTANTIAL. The verdict is not
DUPLICATE, because I found no prior statement of F (or of its tree-only
special case). It is not UNRESOLVED, because the reduction above is explicit
at every step.

## 7. Items noticed in passing (non-binding, for the proof gate)

These do not affect the contribution verdict. They are not a proof audit.

* (6.3) needs $a_nx\ge t_e$ for the exact Pareto formula. This holds since
  $t_e\le n/2$ and $a_n=n^{1/\alpha}$ with $1/\alpha>2$.
* (7.1) and (7.5) use the *annealed* bridge LLN with an indicator. Janson
  Remark 5.3 gives annealed and quenched forms; fine.
* Lemma 5.1 covers parallel-edge 2-cycles ($l_1=l_2=1$). Loop blocks carry
  zero energy, and their darts enter only the mass. Consistent with §1.
* §4.4 "masses at block vertices": the block's own darts at $x_i$ are corners
  carrying children (leaves have $S=1$), so (4.4) accounts for all mass.
  Consistent with `metric:measure`.
* The one-vertex event (all edges loops) has vanishing probability, and the
  convention $\tau_n=0$ is harmless for the limit.

## 8. Repairs (separate from the frozen candidate)

No repair can change the verdict over the unchanged scope. The bridge is
technical whatever proof text is used. If the parent keeps F as a technical
record, these text changes would make the contribution statement accurate.
They are not applied here.

1. Present Lemma 3.1 as a citation of Janson Remark 5.3 plus a mark extension,
   and Lemma 3.2 as a verification of its hypothesis (optionally the
   Chebyshev version in §4.2).
2. Cite Fill–Janson 2104.02715 for $\sum|T_v|^\alpha$, Stufler 2020 for
   decorated trees, and the heavy-tailed matrix / tree-Hardy antecedents.
3. Describe Lemma 5.1 as the standard cut-size tail doubling.
4. State plainly that the theorem is a corollary-level assembly once the source
   representation is given.

A different target with a plausibly substantial bridge would be the regime
$\alpha\in[1/2,1)$. There macroscopic branches and the CRT excursion enter the
extreme law (compare Fill–Janson Thm 1.10(i)). That regime is outside F, and
mentioning it neither repairs nor replaces F.

## 9. Final status

* **Contribution verdict for full F: TECHNICAL.**
* Count implication: F should not be counted as a new substantial result (campaign stays 4/10 as far as this gate is concerned).
* No proof PASS is issued or implied. No worldwide novelty certificate.
* No nested agents. No writes outside this directory (one transient
  `/tmp/fkc` download, moved here and removed). No commits, staging,
  uploads or messages. The frozen candidate is unchanged.
