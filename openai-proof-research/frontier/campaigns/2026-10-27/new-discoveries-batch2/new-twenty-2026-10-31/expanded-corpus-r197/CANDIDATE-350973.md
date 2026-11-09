# CANDIDATE 350973: a quotient dissection whose frieze pattern has a negative entry

Lane: expanded-corpus-r197 (Claude). Status: candidate for root review only. **No credit is claimed.** No Lean was run in this lane. The Lean file in `lean/` is an UNCOMPILED draft.

**Honest credit risk: HIGH.** The reasons are in section 7. In short:

- The literal first sentence of the conjecture is already contradicted by an example printed in the source itself.
- The substantive counterexample, to the quotient-dissection clause, is a small modification of the source's own Example 5.4.
- The source is an unpublished 2021 REU preprint.

## 1. The record

- MathDB 350973, "Positivity conjecture for frieze patterns of type $\Lambda_{p_1,\ldots,p_s}$".
- Raw corpus line: `raw/350973.jsonl`. Chunk, line and hashes are in `extracted.json` and `results.json`.
- Source: E. Banaian and J. Chen, *Periodic Infinite Frieze Patterns of Type $\Lambda_{p_1,\ldots,p_n}$ and Dissections on Annuli*, arXiv:2106.06679. Only v1 exists (12 Jun 2021). No journal version was found. Source TeX: `sources/src-350973.bin`, extracted to `sources/x-350973/main.tex`.
- Source Conjecture 9.5 (`\label{conj:Positive}`, verbatim):
  > The only frieze patterns of Type $\Lambda_{p_1,\ldots,p_s}$ with negative entries are those which fail the realizability test (Proposition \ref{proposition:unrealizability1}). In particular, all quotient dissections yield frieze patterns with positive entries.

  The MathDB statement paraphrases exactly these two sentences.

## 2. Source definitions used (all read in the TeX)

- **Frieze pattern** (Def. 1.1). An array $(m_{i,j})_{j\ge i}$ with $m_{i,i}=0$, $m_{i,i+1}=1$ and the unimodular diamond rule. No positivity is required.
  - The printed indices of the diamond contain a typo: the printed bottom entry $m_{i+1,j+1}$ lies in the same row as the top entry.
  - The standard rule $m_{i,j}m_{i+1,j+1}-m_{i+1,j}m_{i,j+1}=1$ is the one consistent with the source's Lemma 2.4 (Lemma `DivisionFreeFrieze`), $m_{i,j}=m_{j-2,j}m_{i,j-1}-m_{i,j-2}$, and with every frieze printed in the source. Our computation uses Lemma 2.4, and the unimodular rule was checked on every computed diamond.
- **Type $\Lambda_{p_1,\ldots,p_s}$** (Section 2). An infinite frieze pattern whose quiddity entries are sums of positive integral multiples of $\lambda_p=2\cos(\pi/p)$, written $m_{i-1,i+1}=\sum_{p\in A_i}\lambda_p$ with $A_i$ a multiset.
- **Realizability test** (Prop. 4.2). The frieze fails it if either
  1. some $A_i\cap A_{i+1}=\emptyset$, or
  2. some $p$ has more than $p-2$ consecutive indices with $A_i=\{p\}$ while some $A_j\ne\{p\}$.

  It "passes the realizability test" otherwise (line 735).
- **Skeletal frieze pattern.** Every string of consecutive entries $\lambda_p$ has length less than $p-2$.
- **Quotient dissection** (Def. 5.3). Start from a dissection of the annulus $A_{n,m}$. Iteratively identify pairs of subgons of the same size that share a vertex on the outer boundary. It is forbidden to identify two subgons that share an edge, or subgons with all vertices on the outer boundary. The quiddity is $m_{i-1,i+1}=\sum\lambda_p$ over the subgons incident to $v_i$, *using the identifications*.
  - The source's Example 5.4 identifies two squares $a_1,a_2$ sharing both outer vertices of $A_{2,6}$. This turns $(2+2\sqrt2,\,3\sqrt2)$ into $(2+\sqrt2,\,2\sqrt2)$, so each vertex incident to both identified squares loses one $\lambda_4$.

## 3. The counterexample

**Base dissection $D$.** Take the annulus $A_{4,3}$ with outer vertices $v_0,v_1,v_2,v_3$ and inner vertices $w_0,w_1,w_2$. Use the four bridging arcs $v_0w_0$, $v_0w_1$, $v_2w_1$, $v_2w_0$. There are no peripheral arcs, so $D$ is skeletal. The regions between consecutive arcs are:

| region | between arcs | outer edges | inner edges | subgon |
|---|---|---|---|---|
| $R_0$ | $v_0w_0$, $v_0w_1$ | none | $w_0w_1$ | triangle $(v_0,w_0,w_1)$ |
| $R_1$ | $v_0w_1$, $v_2w_1$ | $v_0v_1$, $v_1v_2$ | none | square $(v_0,v_1,v_2,w_1)$ |
| $R_2$ | $v_2w_1$, $v_2w_0$ | none | $w_1w_2$, $w_2w_0$ | square $(v_2,w_1,w_2,w_0)$ |
| $R_3$ | $v_2w_0$, $v_0w_0$ | $v_2v_3$, $v_3v_0$ | none | square $(v_2,v_3,v_0,w_0)$ |

The quiddity of $D$ is $(1+2\sqrt2,\ \sqrt2,\ 3\sqrt2,\ \sqrt2)$. This is an ordinary dissection, so its frieze is positive by the source's Corollary 9.1.

**Quotient $\overline D$.** Identify the squares $R_1$ and $R_3$. The identification is allowed under Def. 5.3:

- They have the same size, 4.
- They share the outer vertices $v_0$ and $v_2$.
- They share no edge: $R_1$ is bounded by arcs $v_0w_1,v_2w_1$, and $R_3$ by arcs $v_2w_0,v_0w_0$.
- Each has an inner vertex.

This is exactly the move of Example 5.4. Vertices $v_0$ and $v_2$ each lose one $\lambda_4$, which gives the quiddity cycle

$$(m_{-1,1},m_{0,2},m_{1,3},m_{2,4})=(1+\sqrt2,\ \sqrt2,\ 2\sqrt2,\ \sqrt2),\qquad A=(\{3,4\},\{4\},\{4,4\},\{4\}).$$

**Negative entry.** Lemma 2.4 gives $m_{i,j+1}=c_jm_{i,j}-m_{i,j-1}$ with $c_j=m_{j-1,j+1}$. Along the diagonal $i=0$, write $(a,b)$ for $a+b\sqrt2$:

$$m_{0,1..12}=(1,0),(0,1),(3,0),(0,2),(1,2),(4,-1),(-5,6),(8,-4),(5,-2),(-12,9),(31,-22),(-32,22).$$

So $m_{0,11}=31-22\sqrt2<0$, since $31^2=961<968=2\cdot22^2$. Equally, $m_{1,12}=31-22\sqrt2<0$.

Rows 2 to 10 contain no negative entry and no zero entry. The exact table is in `outputs/frieze/exact-quotient-example.json`, produced by `scripts/exact_frieze.py`. That run checked all 40 diamonds in its window against the unimodular rule and found 0 failures.

**Properties of this frieze.**

1. *It passes the realizability test.* Consecutive multisets all contain 4. The only singletons are $\{4\}$, in runs of length $1\le p-2=2$.
2. *It is skeletal.* Runs of $\lambda_4$ have length $1<2$.
3. *It fails item (ii) of Prop. 4.4.* Every choice is forced, $p_{i,i+1}=4$. At $i=0$ we have $|A_0|=2$ and $p_{3,0}=p_{0,1}=4$, but 4 has multiplicity 1 in $A_0$. So the source's own Realization Algorithm (Section 5.3, step 4) classifies it as "realizable by a quotient dissection". The explicit $\overline D$ above confirms this without relying on the source's Theorem 5.4.
4. *It is infinite.* This is proved in section 4.
5. *Its decomposition is unique.* The multisets $A_i$ are the only decompositions of the quiddity values into $\lambda_p$'s, so "the" realizability test is unambiguous. The proof is in section 4.

**Monodromy.** The monodromy over a period, $\prod K(c_j)$ with $K(c)=\begin{pmatrix}0&-1\\1&c\end{pmatrix}$, has trace $s=2\sqrt2-2\in(-2,2)$. It is elliptic, which is why the signs oscillate.

So $\overline D$ is a quotient dissection whose frieze pattern has negative entries. This refutes "In particular, all quotient dissections yield frieze patterns with positive entries". It also refutes the first sentence under every reading: the frieze passes the Prop. 4.2 test, and it is realizable in the sense of the source's algorithm.

## 4. Ordinary proofs of the auxiliary claims

**(a) Infinitude: $m_{0,k}\ne0$ for all $k\ge1$, so no row $k\ge2$ is a zero row.**

- *Progression identity.* Let $f(k)=m_{0,k}$ and $g(j)=f(j+8)-s\,f(j+4)+f(j)$ with $s=-2+2\sqrt2$. Because $c$ is 4-periodic, $g$ satisfies the same recurrence $g(j+2)=c_{j+1}g(j+1)-g(j)$ as $f$. Direct computation gives $g(0)=g(1)=0$, so $g\equiv0$.
- *Conjugation.* Apply the ring automorphism $\sigma:\sqrt2\mapsto-\sqrt2$ of $\mathbb Z[\sqrt2]$. For each residue $r\in\{0,1,2,3\}$, the sequence $y_t=\sigma f(4t+r)$ satisfies $y_{t+1}=s'y_t-y_{t-1}$ with $s'=\sigma(s)=-2-2\sqrt2<-2$.
- *Initial pairs.* The pairs $(y_0,y_1)$ are $(0,-2\sqrt2)$, $(1,1-2\sqrt2)$, $(-\sqrt2,4+\sqrt2)$ and $(3,-5-6\sqrt2)$. Each satisfies $y_0y_1\le0$ and $|y_1|>|y_0|$, decided exactly in `outputs/frieze/infinite-check.json`.
- *Induction.* Suppose $y_ty_{t-1}\le0$, $|y_t|>|y_{t-1}|$ and $s'<-2$. Then $s'y_t$ has sign opposite to $y_t$ and modulus at least $2|y_t|$, while $-y_{t-1}$ has modulus less than $|y_t|$. Hence $y_{t+1}y_t<0$ and $|y_{t+1}|>|y_t|$. So $y_t\ne0$ for all $t\ge1$.
- *Conclusion.* Every $k\ge1$ has the form $4t+r$ with $t\ge1$, or $k=r\in\{1,2,3\}$ where $f(r)\ne0$ directly. So $\sigma f(k)\ne0$, hence $f(k)\ne0$.

**(b) Uniqueness of the decomposition.**

- Every $\lambda_p$ lies in $[1,2)$. Also $\lambda_3=1$, $\lambda_4=\sqrt2$, and $\lambda_p\ge\lambda_5=\varphi>\sqrt2$ for $p\ge5$, with $\lambda_p$ increasing in $p$.
- A value $v$ written as a sum of $k$ terms satisfies $k\le v<2k$. So:
  - $\sqrt2$ needs one term, which forces $p=4$.
  - $1+\sqrt2$ needs two terms. If both terms were at least $\varphi$ the sum would be at least $2\varphi>1+\sqrt2$, so the smaller term is $1$ (because $1+1\ne1+\sqrt2$, the other is then $\sqrt2$) or $\sqrt2$ (then the other is $1$, so the multiset is again $\{3,4\}$).
  - $2\sqrt2$ needs two terms, and either $\{4,4\}$ or $1+\lambda_p$ with $\lambda_p=2\sqrt2-1$.
- The second option is impossible because $\lambda_7<2\sqrt2-1<\lambda_8$:
  - $\lambda_8^2=2+\sqrt2>9-4\sqrt2=(2\sqrt2-1)^2$, since $50>49$.
  - $\lambda_7$ is the largest root of $x^3-x^2-2x+1$. That polynomial is positive at $2\sqrt2-1$ (value about 0.113) and negative on the interval between its two larger roots, which contains $[0.45,1.80]$. Alternatively, use $\cos x\le1-x^2/2+\tfrac{5}{96}x^4$ at $x=\pi/7$.

**(c) The frieze generated by a quiddity sequence satisfies the unimodular rule.** Set $D(k)=m_{i,i+k}m_{i+1,i+k+1}-m_{i+1,i+k}m_{i,i+k+1}$. Then $D(1)=1$, and $D(k+1)=D(k)$ because both diagonals $i$ and $i+1$ satisfy the recurrence with the same coefficient $c_{i+k+1}$. This is a three-line `ring` identity.

## 5. Search coverage, prior art and the source's own data

**Searches** (float diagnostics, then an exact check of the reported example):

- `scripts/frieze.py`: all periodic quiddity cycles with $A_i$ multisets of size at most 2 from $\{3,\ldots,p_{\max}\}$, for period at most 4 with $p_{\max}=6$, and period at most 3 with $p_{\max}=10$. For each cycle it checks the test, skeletality and Prop. 4.4(ii). Outputs are in `outputs/frieze/`.
  - Skeletal patterns that pass the test and still have negative entries: the period-3 pattern $(\{5\},\{5\},\{4,5\})$ and six period-4 patterns, including the one above.
- `scripts/quotient.py`: explicit skeletal annulus dissections in the cyclic bridging-arc model, with $n\le5$, $m\le4$, $r\le5$ arcs and one identification. It tested 3,732 quotient dissections and found 6 classes with negative friezes. The smallest has $n=4$, $m=3$ and is the one above.
- `scripts/model_check.py`: shows that the model reproduces the source's Example 5.4 exactly. The regions are $[3,3,4,4,4]$ with $b=(1,1,1,2,1)$, and identifying the two squares gives $(2+\sqrt2,2\sqrt2)$.

**Source-internal conflicts** (zero-credit items, recorded for root):

- The source's own non-skeletal example $(1+\sqrt2,1,2,1+\sqrt2)$ (Section 5.2, "satisfies all conditions" of Prop. 4.4) passes the Prop. 4.2 test. Its frieze has a 0 and a negative entry $-(\sqrt2-1)$ in row 5 (`outputs/frieze/source-example-nonskeletal.json`). So the **literal first sentence of Conjecture 9.5 is already contradicted by the source's own printed example**, and refuting it literally earns zero credit. The intended reading is that negative entries occur only for patterns unrealizable by dissection or quotient dissection. That reading is what the explicit $\overline D$ refutes.
- The source's Theorem 5.4 proof says that at each $j_k$ vertex there are "two distinct outer $p$-subgons". This fails for the skeletal, test-passing $(\{5\},\{5\},\{4,5\})$, where both coincide. That frieze also has negative entries; the first negative row is row 17 and the trace is $\varphi(\sqrt2+\varphi-2)\approx1.67$. A refutation resting only on that would be a correction of the source's theorem (lesson 352827). **Our main example does not use Theorem 5.4**: $\overline D$ is constructed explicitly.

**Literature screened:**

- arXiv:2106.06679 (v1 only).
- Cuntz–Holm–Jørgensen, arXiv:2603.18975 (Mar 2026). It cites Banaian–Chen but studies only positive single-type $\Lambda_p$ infinite friezes; the TeX was grepped for Banaian, conjecture, quotient and negative.
- Andritsch, *A note on friezes of type $\Lambda_p$* (single type).
- Adams–Banaian, arXiv:2509.17258 (title only).
- Web searches found no journal version, thesis revision or later treatment of Conjecture 9.5.
- **Not read:** J. Chen's 2020 UMN REU slides (`Problem6_finaloralreport.pdf`), which a search snippet says contain a positivity lemma for paths on skeletal annulus dissections.

**Registries** (`outputs/registry-screen.json`):

- Lean Pool HEAD `01db1d70` is unchanged. Its FriezePatterns project is Coxeter integral frieze maxima, which is unrelated.
- The Omega HEAD `39783309...` D5 and Problems trees have no frieze hits.
- The OpenAI/math HEAD `4eaee875` is unchanged, and the cached preprint listing has no frieze hits.
- GitHub: 8 repository queries, no relevant hit. The only frieze Lean repository, ElVec1o/vico_counting_friezes, counts positive rational friezes.

## 6. Statement-correspondence plan for Lean (root or Sol stage)

**Literal endpoint (cheap, but zero credit by itself because of section 5).** `¬ Conjecture`, where `Conjecture` says: for every frieze $F$ over $\mathbb R$ that is infinite (no zero row $k\ge2$), periodic and of Type $\Lambda$ with decomposition $A$, if $F$ has a negative entry then $A$ fails Prop. 4.2. The proof exhibits $F$ above with $A$ as in section 3. The `FailsTest` definition transcribes Prop. 4.2, with "more than $p-2$ consecutive" read as at least $p-1$ consecutive.

**Substantive endpoint (recommended).** There exists a quotient dissection of an annulus whose generated frieze is infinite and has a negative entry. Model:

- *Skeletal annulus dissection data.* A cyclic sequence of $r\ge1$ bridging arcs, region $t$ having $a_t\ge0$ outer and $b_t\ge0$ inner boundary edges, with $a_t+b_t\ge1$, $\sum a_t=n$ and $\sum b_t=m$. Subgon size is $a_t+b_t+2$. The outer vertices of region $t$ are $o_t,\ldots,o_t+a_t$ with $o_{t+1}=o_t+a_t$.
- *Admissible identification.* Equal sizes, not cyclically adjacent (adjacent regions share an arc), and a common outer vertex.
- *Quotient quiddity.* At $v$, sum $\lambda$ over the identification classes incident to $v$.

The fidelity argument is that every skeletal dissection of $A_{n,m}$ up to Dehn twist is given by such data. The source itself considers dissections only up to Dehn twist and reads quiddities off subgon incidences. This modelling step is the main fidelity risk and needs an independent statement-fidelity review. The concrete instance is $r=4$, $a=(0,2,0,2)$, $b=(1,0,2,0)$, identify $(1,3)$.

**Lean ingredients** (all elementary):

- Use $\mathbb Z\sqrt2$ (`Zsqrtd 2`) for the exact entries, computed by `decide` or `rfl`.
- Map to $\mathbb R$ through `Zsqrtd.lift ⟨√2, _⟩`.
- $\lambda_3=1$ from `Real.cos_pi_div_three` and $\lambda_4=\sqrt2$ from `Real.cos_pi_div_four`.
- Negativity from $31/22<\sqrt2$ (`Real.lt_sqrt` and `norm_num`).
- Infinitude via the second embedding `Zsqrtd.lift ⟨-√2, _⟩`, the alternating-growth induction, and injectivity of the embedding (`irrational_sqrt_two`).
- The unimodular rule by the induction of 4(c).
- Optional uniqueness of $A$ needs bounds on $\cos(\pi/7)$ and $\cos(\pi/8)$.
- No `native_decide` is needed. The draft is in `lean/BanaianChen350973.lean` (UNCOMPILED).

## 7. Honest assessment

- **Correctness.** High confidence. The arithmetic is exact, the frieze is fixed by Lemma 2.4, and the quotient follows Def. 5.3 and mirrors Example 5.4.
- **Novelty.** No prior statement of a negative quotient-dissection frieze was found. The REU slides are unread.
- **Credit risks:**
  1. The literal record's first sentence is refuted by the source's own example, so the literal negation is source-internal.
  2. The substantive counterexample is a short modification of the printed Example 5.4. It drops one triangle, gives the identified squares two outer edges each, and adds one inner square. This is the "short augmentation of a printed construction" profile (341250, 373598).
  3. The mechanism is the generic one: an elliptic monodromy, $|{\rm tr}|<2$, forces sign changes.
  4. The source is an unpublished REU preprint.
- **Lean cost.** Low for the literal endpoint and moderate for the quotient model.
- **Recommendation.** Root should decide whether the quotient-dissection clause counts as a distinct, substantive target. If it does not, treat this as a recorded refutation with zero credit.
