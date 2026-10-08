# H033 retrieval lookup reviewer report

UNREVIEWED report; its universal rejection is not accepted by root.
Task: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h033-retrieval-lookup-fable-20261008-r1
Provider/model: acpRegistry_factory_droid / claude-fable-5.1.
COMPLETED, no pending children. Corrections/disposition recorded separately.

# H032 R1 lookup-cost residual: scoped negative

**Verdict: scoped negative.** Once the baseline is allowed a competent layout of the *same descriptors* at the *same declared hard peak*, the 3-cell XOR retrieval map has no lookup-time advantage, and the frozen single-batch protocol it requires costs more walk work than continuous insertion. No regime survives in which the lookup saving repays the peel work, let alone the walk penalty. No experiment or benchmark is warranted.

## What I read

Project files (accessed): RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md (H032/H031 sections), H032-memory-retrieval-cards.md, H032-retrieval-capacity-falsifier.md, H031-packed-storage-scope.md, H030-hierarchy-scope.md, H030-partitioned-filter-screen.md, H030-storage-reconciliation.md, H028-layout-admission-gate.md, W004/W008 lookup records. These supply the peak formula, the pointwise-containment argument, and the convention that field hashes and lookups are paid.

Primary source accessed this session: Graf–Lemire, *Xor Filters*, arXiv 1912.08258v3 §3 (HTML). Used facts: array size $c=\lfloor 1.23|S|\rfloor+32$; query is three hash evaluations plus three random memory accesses (Alg. 1); construction is repeat-until-success with freshly chosen hash functions (Alg. 2–3); success probability "always greater than 0.8" for small sets and approaching 1 for large sets (citing Botelho et al. at $10^7$, Molloy); about 19% of cells empty; the authors themselves note other structures "may need fewer memory accesses" and rely on memory-level parallelism.

Recollection, not accessed: Knuth linear-probing expectations, successful $\tfrac12(1+\tfrac{1}{1-\alpha})$ and unsuccessful $\tfrac12(1+\tfrac{1}{(1-\alpha)^2})$; 3-XORSAT peel threshold $c_3\approx1.222$; birthday constant $\sqrt{\pi N/2}$. Dietzfelbinger–Pagh 2008 was read by the original proposer, not by me.

## Notation

$w$ stored endpoints, $m=cw$ cells ($c\ge1$, $c\approx1.23$ practical), $u=\lceil\log_2(w+1)\rceil$, $v=\lceil\log_2(m+1)\rceil$, seed width $s$, tag width $t$, degree width $d$. R1's own declared construction peak (Astra form, checked by root):

$$\Pi = w(4v+u+s+t) + m\cdot\max(d+u+v,\; s+t).$$

DP rate $\theta$; one walk step costs $C_{\text{step}}$ (affine addition with batched inversion, roughly 6 field multiplications plus bookkeeping; no price assigned). One random cache-line fetch costs $c_{\text{line}}$, left symbolic. $N=q/2$ negation classes.

## 1. A hashed descriptor dictionary fits inside R1's own peak

Take an open-addressed linear-probing table of the identical $(3v+s+t)$-bit descriptors at load $\alpha$: space $w(3v+s+t)/\alpha$. It fits under $\Pi$ iff

$$\alpha \;\ge\; \alpha^* = \frac{3v+s+t}{4v+u+s+t+c\cdot\max(d+u+v,\;s+t)}.$$

With $u\approx v=L$, $s=L+\sigma$, and the typical branch $s+t\le d+u+v$:

$$\alpha^* = \frac{4L+\sigma+t}{(6+2c)L+\sigma+t+cd}\;\xrightarrow{L\to\infty}\;\frac{4}{8.46}\approx0.47 .$$

Checked values ($c=1.23,\ \sigma=2,\ t=16,\ d=4$): $L=30\Rightarrow\alpha^*\approx0.50$; $L=40\Rightarrow\alpha^*\approx0.49$. So a dictionary at load $\le 1/2$ sits inside the peak R1 already reserves, with no peel stack and no vertex array. The baseline pays the same signature hashes (same chosen hash, so the earlier pointwise containment of false replays still holds); its slot index is $h_0$ rescaled, no extra hash. Duplicate signatures are detected at insertion, so the baseline does not even need R1's descriptor sort.

## 2. Lookup cost per query

Nearly every query is a nonmember (one useful hit per solve), so the unsuccessful case is what matters.

| Layout, same peak | Memory lines per nonmember query | Dependency | Word work |
|---|---|---|---|
| R1 3-cell XOR (accessed Alg. 1) | 3 random lines, always | independent (MLP) | 3 hashes (common), 2 XORs of $s+t$ bits, $t$-bit compare |
| Linear probing, $\alpha\le1/2$ | expected 2.5 sequential probes $\approx$ 1 line, sometimes 2 adjacent | 1 round trip | 3 hashes (common), $\le$3 compares of $3v$ bits (2 words) |
| Sorted + prefix directory | 2–3 lines | 2 dependent round trips | $\log_2(\text{bucket})$ compares |
| Naive binary search | $\approx\log_2(w/K)$ lines ($K$ = cache-resident entries) | all dependent | $\log_2 w$ compares of $3v$ bits |

Result: $\ell_B(\text{hash}) < \ell_R$ in bandwidth and equal in latency; $\ell_B(\text{directory}) \approx \ell_R$; only the non-competent naive binary search loses to R1. Comparison widths are 1–2 words in every arm; the bit-complexity axis does not separate them. Hash evaluation of the canonical $x$ ($\log p$ bits to three indices) is paid identically by both.

## 3. Build-side costs

Common: generating $w$ endpoints ($w/\theta$ walk steps), signature hashing.
Baseline: $w$ inserts, each about one random line plus a short sequential probe.
R1 (from accessed Alg. 3–4): three random cell updates per key in mapping, three removals per peeled key, three reads plus one write per key in assignment, roughly 9 random lines per key plus queue/stack traffic and the full cell scan, plus the descriptor sort R1 specifies. So $\Delta b \approx 8$ random lines per entry before failure.

Failed peel: with descriptors holding only hashed cell indices, a rehash needs $x$ again, so every retained seed is replayed: $w/\theta$ walk steps, the entire build walk, per failure. Expected penalty $\frac{p_f}{1-p_f}\cdot w/\theta$ steps. The accessed source gives $p_f\le0.2$ for small sets, approaching 0 for large sets without a stated rate. Fair repair available to R1 at no extra space: store a seed-independent $3v$-bit fingerprint of $x$ and derive cell indices by a salted mix, making rehash an $O(w)$ word pass (the source's own remark about hashing keys to 64/128-bit integers). I grant this repair; it removes the replay term but does not change the conclusion. The baseline has no failure mode.

Tag and replay: a tag pass costs one trail replay ($1/\theta$ steps) plus endpoint equality, scalar recovery and $[k]G=Q$ check, identical in both arms. R1's nonmember false-pass rate is about $2^{-t}$ (idealized model, with the caveats already recorded); the tagged baseline's false replays are a pointwise subset (prior finding). An untagged baseline would false-replay at about $w/m^3$ and save $t$ bits per entry, but that comparison is probabilistic rather than pointwise, so I keep the tagged baseline as primary.

## 4. Number of paid queries tied to the useful-hit process

Frozen single batch: build $B$ steps, archive $w=\theta B$ endpoints, then query. Under the idealized independent-uniform landing model (the same conditional model this project uses, not a theorem for actual walks): a build–build collision is found at the end of the sort with probability $1-e^{-B^2/2N}$; otherwise each query step hits an archived trail with probability $B/N$. Expected total steps

$$E[T](x)=\sqrt N\left(x+\frac{e^{-x^2/2}}{x}\right),\quad B=x\sqrt N,$$

minimized near $x\approx1.1$ at $E[T]\approx1.60\sqrt N$, versus $\sqrt{\pi N/2}\approx1.25\sqrt N$ for continuous insertion. The static structure forces about 27% more walk work before any lookup consideration, because query–query collisions are never detected. At the optimum the expected number of queries is $g\approx0.5\theta\sqrt N$ against $w\approx1.1\theta\sqrt N$, so the query/build ratio is

$$r=\frac{g}{w}\approx0.45\ \text{(expected)},\quad\le0.83\ \text{conditional on no build collision}.$$

Forcing $r\gg1$ means a deliberately small archive ($B=\sqrt{N/r}$), which costs $\sqrt N(\sqrt r+1/\sqrt r)$ walk steps: $r=100$ costs 10× the optimum. Large reuse is not available to a single target.

## 5. Break-even

R1's lookup side wins only if

$$r\,(\ell_B-\ell_R)\;\ge\;\Delta b+F_{\text{fail}},\qquad r\approx0.45,\ \Delta b\approx8\ \text{lines}.$$

- Hash baseline: $\ell_B-\ell_R<0$. Never.
- Directory baseline: $\ell_B-\ell_R\approx0$. Never meaningfully.
- Naive binary search: need $\log_2(w/K)-3\ge 18$, i.e. $w\gtrsim 2^{21}K\approx2^{40}$ for $K\approx2^{19}$. Only against a non-competent baseline, and only at an archive of order $2^{40}$ entries.

Converting the lookup side to walk work: the fraction of complete work at stake is at most

$$\theta\cdot\frac{\ell_B-\ell_R}{C_{\text{step}}}\cdot c_{\text{line}},$$

because each query is separated by $1/\theta$ walk steps. For it to even approach the 27% frozen-archive penalty, $\theta$ must be near 1 and the lookup difference must be a sizeable fraction of an EC step. $\theta\approx1$ with $w\approx2^{40}$ means $N\approx2^{80}$ with every visited point stored (about $2^{40}\times23$ bytes), a regime no one runs, and the correct baseline there is a plain hash table of points at 1–2 lines per query. At realistic $\theta\ll1$ the lookup term is invisible.

## 6. Named regime check

The only nominal regime is: naive binary-search baseline, $\theta\approx1$, $w\gtrsim2^{40}$. It fails the brief's requirement of a competent baseline (section 1 shows the hashed dictionary fits the same peak) and sits inside a protocol that already loses $\approx27\%$ walk work. No other regime exists: the inequality in section 5 has no positive solution against the hash or directory baselines for any $r$.

## 7. Cheap decisive test (paper, no run)

An independent reviewer checks two arithmetic facts with the proposer's own widths:

1. $\alpha^*=\dfrac{3v+s+t}{4v+u+s+t+c\max(d+u+v,s+t)}\le\tfrac12$ for $v\ge30$, $t\le32$, $c=1.23$. If true, the dictionary fits R1's declared peak.
2. Per nonmember query, R1 touches exactly 3 random lines (fixed by construction, accessed Alg. 1) while linear probing at $\alpha\le\tfrac12$ touches an expected $\le2$ adjacent lines.

If both hold, no lookup-time gain exists at the same hard peak for any query count. R1 could only be revived by showing $\alpha^*\gtrsim0.8$, which requires $s+t\gg u+v$ (very wide seeds or tags), contradicting its own compact-descriptor premise.

## Side observation, out of this brief

For the deferred resident-only contract: R1's tag is a stored key fingerprint, so its at-rest cost is $1.23(s+t)$ bits per key, while a quotiented dictionary with a $(t+\log_2(w/B))$-bit fingerprint, of which $\log_2(w/B)$ bits are implied by the bucket address, costs about $(s+t+\log_2 B+O(1))/\alpha$ per key. At $\alpha\approx0.8$–0.95 (bucketized cuckoo or Robin Hood) these are within roughly $\pm20\%$. The resident-only capacity question therefore also looks marginal, not multiplicative. This is a paper estimate and needs its own contract; I do not ask root to accept it here.

## Uncertainties retained

- Line counts are structural, not timed; $c_{\text{line}}/C_{\text{step}}$ is left symbolic and no hardware price is asserted.
- The 27% frozen penalty and $r\approx0.45$ come from the idealized uniform-landing model, with the DP tail and actual walk statistics outside it, as in prior H029/H031 caveats.
- Linear-probing expectations assume near-uniform signatures, which holds for the hashed cell indices but is a model assumption.
- Finite-size peel failure rate at large $w$ is not quantified by the accessed source; I granted R1 the fingerprint repair rather than charging the replay term.
- The pointwise containment covers the tagged baseline only; the untagged variant is a probabilistic comparison.

Verified improvement remains NONE. Recommended disposition: record R1's lookup-cost hypothesis as rejected at the hard-peak contract against the hashed descriptor dictionary, keep the resident-only and multi-archive questions as separate unopened contracts, and admit no benchmark.
