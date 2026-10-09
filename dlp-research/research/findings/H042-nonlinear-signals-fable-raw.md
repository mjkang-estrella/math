# H042 nonlinear-signals Fable raw report — UNACCEPTED

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h042-nonlinear-signals-fable-20261009-r1`.
Provider/model: acpRegistry_factory_droid / claude-fable-5.1. Terminal status: completed.
Raw proposer claims below require independent review. The provider usage footer is unverified metadata, not research evidence. No experiments authorized by this report.

# H042 independent ideation: explicit nonlinear public signal-and-decoder

**Role.** Factory `claude-fable-5.1`, read-only in `/home/mj-kang/Documents/Dev/math/dlp-research`. Read RESEARCH_LOOP.md, RESEARCH_TEAM.md, STATE.md (H042/H041 sections and history), H042-independent-briefs.md (briefs only; it contains no proposals), the accepted H041 dispositions (information, primary, fused-work) and the H041 Fable raw report, plus the earlier information-lens dispositions H013, H017, H019, H036, H038, H039, H040 and the H002 learning cards. No other H042 proposal exists in the tree and none was read. No solver runs, imports, edits, children or commits. Primary sources were read through FetchUrl or a read-only `curl | pdftotext` pipe; the two temporary PDF files I created under `/tmp` were deleted.

**Verdict: no new operator from this lens.** Verified improvement remains NONE; the best supported exponent remains 1/2. I examined four genuinely changed operations outside the H041 small-Fourier-L1 autocorrelation and the scoped low-degree Kummer arguments. Each has an explicit public form and an actual extraction step, and each fails on its own complete invoice, not on a universal exclusion. I am not submitting cards. Two narrow lemmas and one ledger item below are new to the record and may be worth retaining as admission accuracy, not as solver evidence.

## Primary reads this task

- Kohel–Shparlinski, *On exponential sums and group generators for elliptic curves over finite fields*, full text of Sections 2–3 (author-hosted PDF, read via pdftotext; FetchUrl rejects PDFs). Proposition 1 (L-polynomial degree $2g-2+\deg \mathfrak f(\chi)$, additivity of conductors for characters ramified in disjoint divisors), Theorem 1 (unramified group character times Artin–Schreier character, bound $\sum m_i\deg P_i\, q^{1/2}$), inequality (3) $|S|\le 2\deg(f)q^{1/2}$, and Corollary 1 (same bound for any subgroup $H$, proved by averaging over characters trivial on $H$). Their $q$ is our $p$.
- Kaluđerović–Kleinjung–Kostić, *Cryptanalysis of the generalised Legendre pseudorandom function*, ANTS XIV (msp.org open-access PDF; the eprint PDF returned an HTML bot page). Contribution section: for the linear Legendre PRF (hidden shift of the Legendre sequence) an $O(p^{1/2})$ attack with $p^{1/4}$ queries, $O(p\log p/M^2)$ with $M$ queries, obtained from the Möbius/affine group action on the key.
- Håstad–Näslund, *The security of all RSA and discrete log bits*, JACM 2004: abstract only (ACM page; the author-hosted PDFs returned HTML). The chosen-multiplier hidden number problem: an oracle guessing the $i$-th bit of $ax \bmod N$ for random $a$ with non-negligible advantage yields $x$ (or a factor of $N$) by a polynomial-time reduction, and the results do not depend on group representation. I did not read the exact polynomial; I treat the reduction as existing, with unstated exponents.

## Operation A: multi-translate Kummer product tests with designed public zero sets

This is the "higher-order with actual extraction" attempt the brief asked for, done in the only way I could make the extraction explicit.

**Public operation.** Fix $m\ge1$ public multipliers $t_i=c_i-1\neq0$ and $m+1$ public rational functions $g_0,\dots,g_m\in\mathbb F_p(E)$ whose odd-valuation supports $D_i$ are sets of points $[a]G$ with index sets $A_i\subset\mathbb Z_q$ chosen by us (existence by Riemann–Roch when $\sum A_i\equiv0$; for $A_i$ an arithmetic progression the product $\prod_{a\in A_i}(x-x([a]G))$ is evaluable in $\tilde O(\sqrt{|A_i|})$ by the baby/giant resultant trick already cited in H041 as the interval-product evaluator). Sample $d$ uniform, compute $P=[d]G$ and $P+[t_i]Q=[d]G+[t_i]Q$, and output the sign

$$\sigma_k(d)=\chi\Big(g_0(P)\prod_{i=1}^m g_i\big(P+[t_i k]G\big)\Big).$$

**Signal.** If the parity multiset $D_0+\sum_i(D_i-[t_ik]G)$ is empty, the product is a constant times a square (under the H041 full-odd-order-group hypothesis the square root is rational), so $\sigma_k(d)$ is constant in $d$. Otherwise, by Kohel–Shparlinski Prop. 1 with a tame Kummer conductor in place of Artin–Schreier (my derivation, same averaging as their Cor. 1 for a proper subgroup), $|\mathbb E_d\sigma_k(d)|\le |{\rm odd\ support}|\cdot\sqrt p/q$. So a handful of samples decides degeneracy exactly: this is a one-shot, sampling-light test, which is what distinguishes it from H041's $\varepsilon^{-2}$ peak search.

**Extraction and the pairing lemma (new, scoped).** Take $D_0$ reduced and nonempty with some index $a_0$. For $k$ to be degenerate the point $[a_0]G$ must be cancelled by a point of some translate, so $a_i-t_ik=a_0$ for some $i\ge1$, $a_i\in A_i$. Hence the degenerate set $K$ satisfies
$$|K|\le S:=\sum_{i\ge1}|A_i|,$$
and $K$ is public, computable from the design in $O(S^2)$ scalar operations. The test therefore decides $k\in K$ exactly; the brief's observation that divisor cancellation alone yields no scalar relation is sharpened to: it yields membership in a public set no larger than the translated support. Partial cancellation gives nothing detectable, since the Weil bound already makes nondegenerate values $O(S/\sqrt q)$.

**Complete cost against baseline.** Each test costs $\tilde O(\sum_i\sqrt{|A_i|})\ge\tilde O(\sqrt S)$ field operations (concavity), plus $m$ scalar multiplications $[t_i]Q$ per design and one addition per re-centering $Q\to Q-[e]G$. Covering $\mathbb Z_q$ needs at least $q/S$ designs, so total work is at least $q/\sqrt S$ even with the square-root structured evaluator, and the detection margin needs $S\ll\sqrt q$, giving $\gg q^{3/4}$. Equal-$S$ comparison: checking $k\in K$ directly by $|K|$ comparisons of $[t_i]Q$ with $[a_i-a_0]G$ costs $O(S)$ group operations with no sampling, so the character test is dominated even before the signal bound. Memory is $\tilde O(\sqrt S)$ per design.

**Prior-art distinction.** Not the H041 autocorrelation (no peak search, no $\varepsilon^{-2}$), not the H040 interval membership (no sign ambiguity: the degenerate set is explicit), and not the H038 compact-coset resultant (characters, not roots). Weil/KS bounds are the only imported facts.

**Unsupported step / falsifier.** There is nothing left to falsify: the pairing lemma caps the list at $S$ and the invoice loses for every $S$. Not carded.

## Operation B: exact translate-correlation by point counting, with an elliptic Prym

**Public operation.** Choose the lag point $T=(c-1)Q$ and align the feature to the halved lag: $A=-[2^{-1}]T$ (free in odd order). Let $h(P)=(x(P)-x_A)(x(P+T)-x_A)$. Its odd support is $\{A,-A\}\cup\{A-T,-A-T\}=\{A,-A,3A,A\}$, i.e. $\{-A,3A\}$ after parity: the double cover $w^2=h$ of $E$ is branched at two points, so it has genus 2 and its Prym is an elliptic curve $E'_A$. Hence
$$\textstyle\sum_{P\in E(\mathbb F_p)}\chi(h(P))=-a_p(E'_A)+O(1),$$
an exact integer obtained by one SEA point count on $E'_A$ (model computable by a polynomial amount of algebra; I have not written it down). This removes the $\varepsilon^{-2}$ sampling entirely and replaces the H038/H040 genus-3/genus-4 covers by a genus-1 trace. We can query the map $\alpha\mapsto a_p(E'_{[\alpha]G})$ at any public affine image $\alpha=\lambda k+\mu$.

**Gain source and the missing decoder.** The signal is a non-translation-invariant public function of the scalar with range about $4\sqrt p$ values, so two or three queries determine $k$ information-theoretically. Extraction means inverting $\alpha\mapsto a_p(E'_{[\alpha]G})$. The decoders I can write: (i) enumerate the isogeny class of trace $a^*$ (about $H(a^{*2}-4p)\approx\sqrt p$ curves, by small-degree isogeny walks) and solve $j(E'_{[\alpha]G})=j$ for each, which is $\ge\sqrt p$ polylog; (ii) batch by a modular polynomial $\Phi_L(j(E'_{[\alpha]G}),j^*)$, which covers about $L$ class members at cost $\tilde O(L)$ root finding, i.e. $N$ hypotheses at cost $N$, worse than BSGS; (iii) treat the trace as a hash and run BSGS on it, which is plain BSGS with each step costing one SEA ($\gtrsim 2^{20}$ group operations at 256-bit $p$).

**Costs.** Per query: one scalar multiplication, model construction, one genus-1 point count. No preprocessing or memory beyond the decoder's; failure only if the model degenerates ($A\in\{O\}\cup E[2]$, excluded in odd order). Baseline: matched-memory BSGS/rho.

**Prior-art distinction.** H038 recorded the convolution point-count operator and H040 the genus-4 fiber product, both without a decoder; the halved-lag alignment to an elliptic Prym is new in the record but changes only the per-evaluation genus, not the inversion problem.

**Unsupported step.** Any structure in the trace-of-fiber map allowing inversion below $\sqrt p$. I know of none and do not claim impossibility; CM-type construction of a curve with prescribed trace is itself class-number work. Cheapest decisive check is paper-only and already done: every decoder I can specify costs at least $\sqrt p$ point counts. Not carded.

## Operation C: hidden-shift framing and the Legendre-PRF comparator (prior-art note, not a mechanism)

Every statistic of $F(n)=f([n]G)$ queried at $k+d$ or $\lambda k+\mu$ is a hidden-shift problem for a public sequence on $\mathbb Z_q$. The freshly read KKK paper is the strongest classical comparator I know: with the full affine/Möbius symmetry of the Legendre sequence they reach $O(p^{1/2})$ with $p^{1/4}$ queries, or $O(p\log p/M^2)$ with $M$ queries, by trading queries for symmetric images of windows. The elliptic sequence has only the negation symmetry for an ordinary generic curve, so the same trade cannot even reach their exponent, and their best case is still square-root. This is a distinction, not a bound on other decoders; I record it so a future "symmetry-expanded window" proposal is measured against the right primary source.

## Operation D: learned bit predictor with the Håstad–Näslund extraction (costed, not submitted)

The brief rejects general learned-feature exclusions and asks for training, calibration, test costs and a holdout mechanism if a learned mechanism is offered. The honest shape of such a card is:

- **Decoder exists.** By the HN abstract, an oracle guessing the $i$-th bit of $a k \bmod q$ for random public $a$ with non-negligible advantage $\varepsilon$ yields $k$ by a polynomial-time, representation-independent reduction (chosen-multiplier HNP). Each oracle call is one scalar multiplication $[a]Q$ (+ optional $[b]G$), feature extraction, and one inference. So the entire mechanism reduces to the predictor; "compact circuit with advantage" and "solver" are the same object.
- **Paid protocol.** Train on $N$ fresh known scalars ($N\cdot(\approx1.5\log_2 q)$ additions without a fixed-base table, or table setup charged), features = coordinates of a few public affine images of the point; disjoint holdout of $N_v$ scalars with permutation-label control; advantage estimate with confidence $\pm N_v^{-1/2}$; extraction cost poly$(\log q,1/\varepsilon)$ calls (exponent not read). Gain iff training + extraction $<$ matched BSGS/rho work. No inverse table: generalization is enforced by disjoint holdout scalars.
- **Cheapest falsifier within cap.** $q\approx2^{20}$, $N=2\cdot10^4$, $N_v=10^4$, one fixed small model class: about $9\cdot10^5$ additions plus features, detects $\varepsilon\ge0.03$ at $3\sigma$; a null excludes only that class and size.
- **Why not submitted.** I cannot name a training prior that predicts advantage; algebraic priors return to characters (bounded by KS for bounded degree and L1), and non-algebraic cheap features have no mechanism. This is H002's L1/L2 card with its extraction half made explicit, not a new operator. Root may attach the HN extraction note to that card if it is ever revived.

## Considered and not carded

| Operation | Why not |
|---|---|
| Two-fold sumset membership by resultant: $\gcd\big(\prod_{a\in A}S_3(x_Q,x_a,Y),\ \prod_{b\in A}(Y-x_b)\big)$ in $\tilde O(B)$ tests $k\in\pm A\pm A$ | List size $\le 2B^2$ only for Sidon-like $A$, where no square-root product trick applies; for progressions the sumset collapses to an interval. Either way list-per-cost is $\tilde O(\sqrt{\text{list}})$, BSGS parity at equal memory. Higher folds blow up resultant degrees ($B^{m-1}$); that is the decomposition lane assigned to Astra. |
| Cheap high-degree features (composite isogenies, power maps $x^e$) to escape the KS degree bound | Isogenies are homomorphisms, so correlations pull back to degree-4 sums on the codomain; $x^e$ has effective degree $\gcd(e,p-1)$ for additive characters. Escaping an upper bound creates no signal; I am not proposing a new capacity threshold. |
| $p$-adic torsion lifts | Every order-$q$ point has a unique order-$q$ lift to $\tilde E(\mathbb Z_p)$, on which the formal logarithm vanishes; information appears only when $q=p$ (anomalous, excluded). |
| Dilation statistics $\mathbb E_d f([d]Q)\bar f([cd]Q)$ | Independent of $k$ after substitution; only mixed additive/multiplicative queries see $k$, which is Operation A or H013. |
| Endomorphism/Frobenius eigenvalue signals | Trivial on $E(\mathbb F_p)$; smooth-norm endomorphisms give GLV constants, not collision-class reductions (H036 norm lemma already scopes this). |

## What is new for the record

1. Pairing lemma: multi-translate Kummer degeneracy tests decide membership in a public set of size at most the translated odd support $S$, and total work is at least $q/\sqrt S$ even with square-root structured products. Scoped to quadratic (or any fixed-order) multiplicative characters of rational functions on prime-order groups; not a statement about other statistics.
2. Halved-lag alignment makes the exact translate correlation an elliptic trace (genus-2 cover, elliptic Prym), computable by one genus-1 point count per query; the decoder is an inverse-trace problem whose known solutions cost at least $\sqrt p$.
3. Ledger note: for learned predictors the extraction side is supplied by the HN chosen-multiplier reduction; the only open item in any such card is the predictor itself and its holdout-verified advantage.

**Status for root.** No candidate admitted, no experiment proposed, no universal exclusion asserted. Access notes: FetchUrl cannot read PDFs; KS and KKK were read through a read-only shell pipe; the eprint PDF host served an HTML challenge page, so the msp.org open-access version was used; Håstad–Näslund full text was not accessible, abstract only. Provider/model actually run: Factory `claude-fable-5.1`.

---
*Factory usage — local bridge. This turn: 1,983,121 tokens · ≈3,240,208 Factory credits. Saved session total: 1,983,121 tokens · ≈3,240,208 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
