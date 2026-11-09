# CANDIDATE 362785: full proof of the induced-path conjecture for the graphs G_{q,p}

Status: candidate only. The ordinary proof below is complete. Computation checks it independently for q ≤ 11 (the combinatorial step) and q = 7 (the whole statement). There is no Lean certificate: this lane may not run Lean. The draft Lean file `lean/InducedPathGqp.lean` is UNCOMPILED. No credit is claimed; root decides.

## 1. Exact target

**MathDB 362785**, "The induced-path conjecture for the graphs $G_{q,p}$". The literal record is in `raw/362785.jsonl`:
- chunk `mathdb-normalized-chunk-*.jsonl`, line and hashes as in `results.json` → `362785.provenance`.

The literal statement reads: "Let $q\geq 3$ be odd, let $p\geq 1$, and let $G_{q,p}$ be the graph constructed in the paper. … **Induced-path conjecture.** For every $p\geq 1$, the graph $G_{q,p}$ is $P_{3q-2}$-free."

**Source.** Goedgebeur, Jooken, Okrasa, Rzążewski, Schaudt, *Minimal obstructions to $C_5$-coloring in hereditary graph classes*, arXiv:2404.11704. The current version is v2 (20 Mar 2026), fetched 2026-11-04 (`sources/362785-abs.html`, e-print `sources/eprint/362785.tgz`, TeX `sources/tex-362785/main.tex`). The conjecture is Conjecture `con:path`, at lines 1757-1759 of main.tex: "Let $q \geq 3$ be odd. For every $p \geq 1$, the graph $G_{q,p}$ is $P_{3q-2}$-free." It is still open in v2.

**Source definition** (main.tex line 1522). For odd $q\ge 3$ and $p\ge1$, $G_{q,p}$ has vertex set $[qp-3]_0=\{0,\dots,qp-3\}$, with arithmetic modulo $n:=qp-2$, and
$N(i)=\{i-1,i+1\}\cup\{i+qj-1 : j\in[p-1]\}$.

This neighbourhood relation is already symmetric: $j=i+qk-1$ gives $i=j+q(p-k)-1$ with $p-k\in[p-1]$, because $(qk-1)+(q(p-k)-1)=n$. So $G_{q,p}$ is the circulant on $\mathbb Z_n$ with connection set $\{\pm1\}\cup\{qk-1: 1\le k\le p-1\}$. `scripts/gqp.py::check_def` checks this edge set against the printed $N(i)$ for every tested $(q,p)$.

**What the source already knows.**
- $q=3$: $G_{3,p}$ is $P_7$-free, from Chudnovsky–Goedgebeur–Schaudt–Zhong (JCTB 2020), cited at line 1754.
- $q=5$: $G_{5,p}$ is $P_{13}$-free, by the source's computer search (lines 1741-1747).
- General $q$: the source proves only $P_{3q-1}$-freeness (Lemma `lem:infinite-easybounds`, via $qK_2$-freeness, Lemma `lem:qk2-free`).
- Sharpness: Lemma `lem:lowerpath` shows $P_{3q-3}\subseteq G_{q,p}$ for $p\ge 2q+1$.

So the conjecture is open exactly for odd $q\ge 7$.

## 2. Theorem

**Theorem.** For every odd $q\ge3$ and every $p\ge1$, $G_{q,p}$ has no induced subgraph isomorphic to $P_{3q-2}$. By Lemma `lem:lowerpath` of the source, the bound is best possible.

## 3. Proof

Write $L=3q-2$ and $n=qp-2$, and suppose $U\subseteq V(G_{q,p})$ induces a path on $L$ vertices.

### Step 0: small $p$
- If $p\le2$, then $n\le 2q-2<L$, which is impossible.
- If $p=3$, then $n=L$, so $U=V$ and $G_{q,3}$ would be a path. But $G_{q,3}$ contains the Hamiltonian cycle $0,1,\dots,n-1$, with $n\ge7$, so it has at least $n>L-1$ edges. Contradiction.
- If $p\ge4$, then $n>L$. Translations $i\mapsto i+c$ are automorphisms, so we may assume $n-1\notin U$, that is, $U\subseteq[0,n-2]$.

### Step 1: linear model
Let $0\le i<j\le n-2$, so $1\le j-i\le n-2$.
- The connection set taken modulo $n$, intersected with $[1,n-1]$, equals $\{1,n-1\}\cup\{qk-1:1\le k\le p-1\}$, because $n-(qk-1)=q(p-k)-1$.
- Hence $i\sim j$ if and only if $j-i=1$ or $j-i=qk-1$ for some $1\le k\le p-1$.
- Since $j-i\le qp-4<qp-1$, this is equivalent to: **$j-i=1$ or $j-i\equiv-1 \pmod q$**.

### Step 2: residues
Write $\rho(v)=v \bmod q\in\mathbb Z_q$. Let $u,w\in[0,n-2]$ with $\rho(u)=\rho(w)+1$.
- (a) If $u<w$, then $w-u\equiv-1$, so $u\sim w$.
- (b) If $u>w$, then $u\sim w$ if and only if $u=w+1$. Otherwise $u-w\equiv1\pmod q$ and $u-w\ne1$, so $u\ge w+q+1$.
- If $\rho(u)-\rho(w)\notin\{\pm1\}$, then $u\not\sim w$. This uses $q\ge3$, so that $+1\ne-1$.

In particular: **if $\rho(u)=\rho(w)+1$ and $u\not\sim w$, then $u>w$**. Call this (★).

### Lemma A (no independent transversal)
No independent set $I\subseteq[0,n-2]$ of $G_{q,p}$ meets every residue class.

*Proof.* Pick $v_s\in I$ with $\rho(v_s)=s$ for each $s\in\mathbb Z_q$. By (★), $v_{s+1}>v_s$ for every $s$, so $v_0<v_1<\dots<v_{q-1}<v_0$. ∎

Let $x_0,\dots,x_{L-1}$ be the vertices of the induced path in path order, and let $r_i=\rho(x_i)$. Since consecutive vertices are adjacent, $r_{i+1}-r_i\in\{\pm1\}$. The *class* of the edge $e_i=x_{i-1}x_i$ ($1\le i\le L-1$) is $\kappa_i=\{r_{i-1},r_i\}$, a pair $\{s,s+1\}$ of cyclically adjacent residues. Because the path is induced, two path vertices are adjacent exactly when they are consecutive.

### Lemma B (the source's Claim `cla:one-edge`, in path form)
If $i+3\le j$, then $\kappa_i\ne\kappa_j$.

*Proof.* The four vertices $x_{i-1},x_i,x_{j-1},x_j$ are distinct, and every cross pair is non-consecutive, hence non-adjacent. Suppose both classes equal $\{s,s+1\}$. Name the endpoints $a,c$ (residue $s+1$) and $b,d$ (residue $s$), with edges $ab$ and $cd$.

By (★) and Step 2(b), the non-adjacent pairs $(a,d)$ and $(c,b)$ give $a\ge d+q+1$ and $c\ge b+q+1$. By Step 2, the edge $ab$ means $a<b$ or $a=b+1$, and likewise for $cd$.
- If $a<b$: then $d<a<b<c$. So $cd$ needs $c=d+1$, but $d<a<d+1$ is impossible.
- If $a=b+1$: then $d\le b-q<b<c$. So $c=d+1\le b-q+1<b$, contradicting $c\ge b+q+1$. ∎

### Lemma C (run structure)

**(i) Each class occupies one run of length at most 3.** If $\kappa_i=\kappa_j$ with $i<j$, then $j\le i+2$ by Lemma B. If $j=i+2$, then $r_i\in\kappa_i$ and $r_{i+1}\in\kappa_{i+2}=\kappa_i$, so $\kappa_{i+1}=\{r_i,r_{i+1}\}=\kappa_i$. Hence the indices carrying a given class form one interval ("run") of length $\le3$. Let $R_1,\dots,R_t$ be the runs in path order and $K_1,\dots,K_t$ their classes, which are pairwise distinct.

**(ii) The runs move monotonically around the cycle.** Consecutive runs meet at a vertex $x_\beta$, and $K_m,K_{m+1}$ are distinct classes containing $r_\beta$. So $K_{m+1}=K_m+\delta_m$ with $\delta_m=\pm1$ (shifting the pair by $\delta_m$). If $\delta_{m+1}=-\delta_m$, then $K_{m+2}=K_m$, contradicting distinctness; this also holds for $q=3$. So all $\delta_m$ are equal. Reversing the path if necessary, $K_m=\{s_0+m-1,\,s_0+m\}$ for all $m$. Distinctness then gives $t\le q$.

**(iii) Boundary vertices and run lengths.**
- Let $\beta_m=|R_1|+\dots+|R_m|$ and $B_m=x_{\beta_m}$. Then $\rho(B_m)=s_0+m$ for $1\le m\le t-1$.
- An interior run $R_m$ ($2\le m\le t-1$) goes from residue $s_0+m-1$ to residue $s_0+m$, alternating between them. So $|R_m|$ is odd, hence $|R_m|\in\{1,3\}$.
- $R_1$ ends at residue $s_0+1$, and $R_t$ starts at residue $s_0+t-1$.

### Main argument
We have $\sum_m|R_m|=L-1=3q-3$. In every case below we exhibit an independent set of path vertices, that is, pairwise non-consecutive indices, meeting every residue class. That contradicts Lemma A.

**Case $t\le q-1$.** Here $3q-3\le3t\le3q-3$, so $t=q-1\ (\ge2)$ and every run has length 3. Then $r_0=s_0$ and $\rho(x_{3m})=s_0+m$ for $0\le m\le q-1$. The set $\{x_0,x_3,\dots,x_{3q-3}\}$ is the required independent transversal.

**Case $t=q$.** Let the deficits be $d_m=3-|R_m|\ge0$, so $\sum d_m=3$. Interior deficits lie in $\{0,2\}$ and end deficits in $\{0,1,2\}$. So exactly one of the following holds:
- (I) exactly one interior run $R_k$ ($2\le k\le q-1$) has length 1, and $\{|R_1|,|R_q|\}=\{2,3\}$;
- (II) every interior run has length 3, and $(|R_1|,|R_q|)\in\{(1,2),(2,1)\}$.

Notation, all inside runs of length 3:
- $F_m:=x_{\beta_m-2}$, the first interior vertex of $R_m$, with residue $s_0+m$;
- $G_m:=x_{\beta_m+2}$, the second interior vertex of $R_{m+1}$, with residue $s_0+m$.

$F_1=x_{\beta_1-2}$ exists, with residue $s_0+1$, whenever $|R_1|\ge2$. $G_{q-1}=x_{\beta_{q-1}+2}$ exists, with residue $s_0-1$, whenever $|R_q|\ge2$. The last run $R_q$ has class $\{s_0-1,s_0\}$ and starts at residue $s_0-1$.

- **(I.a)** $|R_1|=3$, $|R_q|=2$. Take $x_0$ (residue $s_0$), $B_m$ for $1\le m\le k-1$, and $G_m$ for $k\le m\le q-1$. The indices are $0,\beta_1=3,\dots$ with all successive gaps equal to 3. For the junction, $\beta_k+2-\beta_{k-1}=3$ because $|R_k|=1$.
- **(I.b)** $|R_1|=2$, $|R_q|=3$. Take $x_{L-1}$ (residue $s_0$), $F_m$ for $1\le m\le k-1$ (with $F_1=x_0$), and $B_m$ for $k\le m\le q-1$. All gaps are 3: the junction gap is $\beta_k-(\beta_{k-1}-2)=3$, and the final gap is $L-1-\beta_{q-1}=3$.
- **(II.a)** $(1,2)$. Take $x_0$ (residue $s_0$; here $B_1=x_1$) and $G_m$ for $1\le m\le q-1$. The indices are $0,3,6,\dots,L-1$.
- **(II.b)** $(2,1)$. Take $F_m$ for $1\le m\le q-1$ (with $F_1=x_0$) and $x_{L-1}$ (residue $s_0$). The indices are $0,3,\dots,L-4,L-1$.

In each case the chosen indices pairwise differ by at least 3, so the set is independent, and it meets all of $\mathbb Z_q$. This contradicts Lemma A. ∎

**Remark.** An induced $P_{L'}$ with $L'\ge 3q-2$ contains an induced $P_{3q-2}$, so the theorem is exactly the conjecture.

## 4. Independent computational checks
All runs used capped `python3 -I` under `scripts/cap.sh` (RSS 1.5 GiB, CPU 120 s, wall 140 s), one process at a time. Logs are in `logs/`.

1. **Combinatorial step** (`scripts/walkcheck.py`, `logs/walkcheck.log`). The script enumerates every ±1 residue walk of length $L$ on $\mathbb Z_q$ that satisfies Lemma B, starting at residue 0, for $q=3,5,7,9,11$.
   - At $L=3q-2$: there are $4q-2$ such walks (10, 18, 26, 34, 42). Every one has an independent transversal.
   - At $L=3q-3$: no walk has one. This matches the sharpness of the theorem.
   - The count $4q-2$ is exactly the case list above: one walk for $t=q-1$, two for (II), and $2(q-2)$ for (I), times two directions.
2. **Whole statement for $q=5,7$ in the infinite linear model** (`scripts/lamq.py`, `lamq2.py`, `lamq3.py`). By Steps 0–1, induced subgraphs of $G_{q,p}$ (for $p\ge4$) are exactly the finite induced subgraphs of the graph $\Lambda_q$ on $\mathbb Z$ with $i<j$ adjacent iff $j-i=1$ or $j-i\equiv-1\pmod q$.
   - $q=3$: maximum 6. $q=5$: maximum 12. Both reproduce the known results.
   - $q=7$: an induced $P_{18}$ exists. The search for $P_{19}$ is exhaustive over all 3261 depth-5 prefixes, about 64 million nodes in 8 chunks (`logs/lamq3-q7-chunks.log`), and finds none.
3. **Direct circulant search** (`scripts/gqp.py`, `logs/gqp-q5.log`, `logs/gqp-q7-a.log`).
   - For $q=5$, $p\le14$ (the source's finite reduction, Corollary `cor:reducetofinite`), the longest induced path has 12 vertices, as the source states.
   - For $q=7$, the search is complete for $p\le8$ (maximum 16) and timed out for $9\le p\le11$, with no path longer than 16 found.

## 5. Prior art and registry screen (2026-11-04)
- **Source v2 (Mar 2026)** still states the conjecture as open. The abstract page and TeX were read; the conjecture and evidence paragraph are at lines 1736-1759.
- **Web search** for the authors, $G_{q,p}$ and the $P_{3q-2}$ conjecture found only the paper and its MFCS 2024 extended abstract. No citing resolution was found. Limitation: this was a single standard web search, not a citation-database crawl, since there is no Scholar access.
- **Lean Pool** (HEAD 01db1d7049cf9668bda1e9e106875ee1278b43e6, unchanged): no hit for 2404.11704, 362785, Goedgebeur, $C_5$-colouring, minimal obstruction, Pokrovskiy or induced path.
- **GitHub repository search**: "C5-coloring", "2404.11704" and "minimal obstructions coloring lean" returned 0 results. "induced path lean graph" returned only KitaKen1/wowii-graph-conjecture-31-lean, which is unrelated (a WoWII conjecture).
- **Omega** live HEAD d9631873d125955c8434f12e8695256148a72857 (moved from root's f1c20718 today). The compare listing is capped at 300 files over 166 commits; no related path was seen. **OpenAI/math** HEAD 4eaee875 is unchanged.

Details are in `outputs/registry-screen.json`.

## 6. Honest credit-risk assessment
- **Source ingredients.** Lemma B is the source's Claim `cla:one-edge` (used there for induced matchings), applied to two path edges. Lemma A is a simplified independent-set analogue of the source's cyclic Claim `clm:ordering`. Step 1, the linear description, is the source's Observation `obs:neighbors`.
- **New part.** The independent-transversal reformulation, the run-structure lemma, and the exhaustive case analysis showing that $3q-3$ edges force an independent transversal. This is about one page.
- **Risk.** The source authors did not find this argument and left the conjecture open in their 2026 v2. Even so, root may judge it a short extension of the source's $qK_2$ machinery: the r94, r97 and 336565 "new part under a page" profile. I rate the credit risk **moderate to high**. The argument settles the conjecture in full scope (all odd $q$, all $p$), not a special case.
- **Significance.** Moderate. The conjecture is about the sharp induced-path length in the source's infinite family of minimal obstructions to $H$-colouring of odd girth $q$. It refines the source's Theorem `thm:infinite-gen` from $P_{3q-1}$ to the optimal $P_{3q-2}$.

## 7. Lean plan (for root and a Sol worker; NOT run in this lane)
File `lean/InducedPathGqp.lean`, marked UNCOMPILED, contains the definitions, the literal statement and the lemma skeleton.

**Statement correspondence.**
- `Gqp q p : SimpleGraph (ZMod (q*p-2))`, with `Adj i j := i ≠ j ∧ (j - i ∈ {1, -1} ∨ ∃ k ∈ Finset.Icc 1 (p-1), j - i = (q*k - 1 : ZMod _) ∨ i - j = (q*k-1 : ZMod _))`. This is the symmetric closure of the printed $N(i)$; the printed relation is already symmetric, as noted in §1.
- "$P_t$-free" is `IsEmpty (SimpleGraph.pathGraph t ↪g Gqp q p)`. Mathlib's `↪g` is an *induced* embedding, since `Embedding` preserves adjacency in both directions.
- The theorem is `∀ q p, Odd q → 3 ≤ q → 1 ≤ p → IsEmpty (pathGraph (3*q-2) ↪g Gqp q p)`.

**Proof route.**
1. Step 0: cardinality for $p\le3$, plus the Hamiltonian-cycle edge count for $p=3$.
2. Transport by translation, so that `n-1` is not in the image.
3. Read the adjacency on `Fin (n-1)` as the linear rule (Step 1).
4. Prove (★), Lemmas A, B and C.
5. Do the case analysis on run lengths. A practical alternative: encode the walk as a `Fin (3q-3) → Bool` step sequence, and prove that Lemma B forces membership in the explicit list of $4q-2$ walk shapes. Then exhibit the transversal for each shape.

Expected size: about 1.5–3 k lines. No `decide` on large objects is needed, because the proof is uniform in $q$.
