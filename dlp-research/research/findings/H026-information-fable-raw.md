# H026 information proposals — raw and unaccepted pending scope review

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h026-information-design-fable-20261008-r1

Root triage: do not adopt the claimed universal two-category classification,
standing predictor gate, spectral identity, endomorphism barrier, or blanket
Galois/p-adic closures. Grid-anchor success differs from arbitrary-origin window
agreement without extra hypotheses; [u]Q is computable by ordinary scalar
multiplication; arbitrary rational-map fibers are not kernel cosets; vanishing
of a torsion logarithm does not make every invariant constant. No optional
numerical test is admitted. Separate reviews must resolve these objections.

# H026 information / learned-mechanism lens (Factory Fable 5.1 replacement role)

**Outcome: scoped no-survivor for this lens, with one exact conversion that any future information or learned proposal must pass, two closures new to the record, and one optional bounded exact falsifier.** Verified improvement remains NONE; the square-root reference is unchanged. Nothing here is a benchmark, a hardware claim, or a Lean claim.

Process: read-only. I read README, RESEARCH_LOOP, RESEARCH_TEAM, STATE, and the information-lens records (H002 learning cards, H003 noisy/Fourier, H013 MCL, H014 screen, H015 preprocessing baseline, H017/H018/H019 information dispositions, H020 public-signal raw, H024 information raw). I did not open `hypotheses/H026-independent-candidates.md` or any other H026 proposal. No edits, experiments, children, imports, or commits. Three primary sources were read this pass through `curl | pdftotext` to stdout (no files written) and `FetchUrl`; everything else cited is marked memory/unverified.

## 0. Framing: what every mechanism in this lens reduces to

Write $P_n=[n]G$, $Q=P_k$. Any public computation on $Q$ yields values of functions $H(P_n)$ at $n=k$ (and at $k+j$, $ck$, $\varphi$-images, …, all cheap). A mechanism in this lens helps only if, as a function of the scalar $n$, $h(n)=H(P_n)$ has structure a decoder can use. There are exactly two kinds of usable structure:

- **(P1) Low-frequency structure:** $h$ has a heavy scalar-Fourier coefficient (H003 route) or a constant fraction of its energy at frequencies $|a|\le q/\Delta$ (window stability). Card 1 gives the exact conversion and the exact bar.
- **(P2) Structured-set membership:** a sublinear test for "$P\in\{[\delta]G:|\delta|\le\Delta\}$". This is **circular**: $\log\Delta$ such tests solve the width-$\Delta$ interval ECDLP, and with $\Delta=q$ it is the full problem. P2 is not an independent primitive and I drop it.

Also a distinction the brief asked for: all cards below use only public points with scalars we chose; calibration on known-scalar points is advice to be charged and amortized, never a target-secret oracle. An exhaustive $\Omega(q)$ calibration table is a diagnostic, not an online component.

## Card 1 — Window-stability bucketing: the exact conversion and bar (conditional; no $H$ supplied)

**Mechanism (public-Q computation and exact recovery).** Fix a window length $\Delta$ and a cheap bucket function $H:\langle G\rangle\to[B]$ with $B\approx q/\Delta$. Table: anchors $A_i=[i\Delta]G$, $0\le i<q/\Delta$, stored under key $H(A_i)$. Online: compute $H(Q)$, take the anchors in that bucket, and for each solve $Q-A_i=[\delta]G$ with $|\delta|<\Delta$ by local BSGS (one shared baby table of size $\sqrt\Delta$). Verify $[k]G=Q$. On failure rerandomize $Q\leftarrow Q+[r]G$ and repeat; this makes the true offset uniform in the window, so success per attempt is exactly the window-agreement probability
$$\varepsilon_\Delta(H)=\Pr_{n,\ 0<\delta<\Delta}\big[H(P_n)=H(P_{n+\delta})\big].$$
Recovery is exact; a bad $H$ only costs time.

**Ledger (group operations, $c_H$ = cost of one $H$ evaluation).** Table $(q/\Delta)(1+c_H)$, memory $q/\Delta$ keys; baby table $\sqrt\Delta$; online $\varepsilon_\Delta^{-1}\big(c_H+(1+\text{false anchors})\cdot O(\sqrt\Delta)\big)$ with false anchors $\approx (q/\Delta)/B\approx 1$. Chance level is $1/B=\Delta/q$, which gives online $q/\sqrt\Delta\ge\sqrt q$: no excess, no gain.

**Gain conditions.** Single target (table charged): need $\Delta\gg\sqrt q$ and $\varepsilon_\Delta\gg\sqrt{\Delta/q}$. With $\varepsilon=\Theta(1)$ at $\Delta=q^{2/3}$ the total is $O(q^{1/3})$. Amortized table (multi-target): the online condition alone, but note the generic preprocessing tradeoff $ST^2\approx q$ (Corrigan-Gibbs–Kogan, already in H002; Bernstein–Lange cube-root, H015) is matched, not beaten, unless $\varepsilon_\Delta\gg\sqrt{\Delta}/q^{1/3}$ at the chosen $\Delta$. Few buckets ($B=2^b$) recovers "predict $b$ coarse bits then block-search", i.e. the same object as the unreviewed H024 posterior-ordering card; many buckets is the new end.

**Why this is the weakest usable signal.** It needs only short-range translation stability of $H$, not an approximate homomorphism (H020 card 2's translation-searchable filter) and not a multiplicative-orbit invariant (H017 card 3). The window statistic is exactly H019's repaired $F_L$ identity: $\varepsilon_\Delta-1/B$ is the energy of the bucket indicators in the band $|a|\lesssim q/\Delta$. So this card gives the algorithmic meaning of that statistic and a one-line admission gate for any future predictor: **state $\Delta$, $B$, $c_H$, and the fresh-sample $\varepsilon_\Delta$; admit only if $\varepsilon_\Delta\gg\sqrt{\Delta/q}$.**

**What known bounds close (verified this pass).** Kohel–Shparlinski, Theorem 1 and Corollary 1 (author PDF read): for any nontrivial additive character $\psi$, any character $\omega$ of the group, and any $f\in\mathbb F_p(E)$ of pole degree $d$, $|\sum_{P\in H}\omega(P)\psi(f(P))|\le 2d\sqrt q$ for every subgroup $H$. Hence for $H=\beta\circ f$ with $\beta$ a bucket map of Fourier $L^1$ norm $L$ on $\mathbb F_p$ (intervals $O(\log p)$, bits $O(\log^2 p)$ by H019), every normalized scalar-Fourier coefficient of each bucket indicator is $\le 2dL/\sqrt q$. Summing over $B$ buckets and the band gives excess $\le 8d^2L^2B^2/q$ at $\Delta=q/B$. Against the requirement $1/\sqrt B$, this **closes $B\ll q^{2/5}(dL)^{-4/5}$**, i.e. all coarse-bit predictors and all windows $\Delta\gg q^{3/5}$, for low-degree $H$.

**Homomorphic transport lemma (my derivation, elementary; sharpens H024 raw card B).** If $\varphi:E\to E'$ is any $\mathbb F_p$-isogeny or dilation $[m]$ with $q\nmid\deg\varphi$, then $\varphi(P_n)=[n]\varphi(G)$ and $\sum_n e_q(an)\psi(f'(\varphi(P_n)))$ is a Kohel–Shparlinski sum on $E'$ with the degree of $f'$, not of $f'\circ\varphi$. So *every* single view through dilations of any height or isogeny chains of any length stays inside the bound above. H024's "small-height dilations" caveat is unnecessary; the bound is invariant under all homomorphic compositions. Only (i) nonlinear mixtures of two or more such views inside one predicate, (ii) iterated non-group maps on $\mathbb F_p$, and (iii) multiplicative characters escape the *statement*; for (iii) the Kummer analogue of Theorem 1 is standard but I did not read it in a primary source this pass, and the multiplicative-scalar-character side keeps only the $q^{-1/12}$ bound already recorded in H013. For (i) and (ii) the bound is merely vacuous; no positive rationale exists.

**Formally open regime.** For low-degree, low-$L^1$ $H$, bucket counts $B\in[q^{2/5},q^{1/2}]$ ($\Delta\in[q^{1/2},q^{3/5}]$) are not excluded by Kohel–Shparlinski plus Erdős–Turán–Koksma; the pair-discrepancy error $O(B\log^2p/\sqrt q)$ is right at the threshold there. Heuristically the excess is zero (the pair $(x(P),x(P+[\delta]G))$ lies on a bidegree-(2,2) correspondence and behaves like a random pair at scale $\Delta$), so this is a loophole of the theorems, not evidence.

**Main unsupported assumption:** that some cheap $H$ has $\varepsilon_\Delta\gg\sqrt{\Delta/q}$ at any $\Delta\ge\sqrt q$. None is supplied; I expect none.

**Cheapest decisive falsifier (optional; root may decline as negative-expectation).** One synthetic prime-order curve with $q\approx3\cdot10^4$, $\Delta=\lceil q^{2/3}\rceil$, $B=\lceil q/\Delta\rceil$; two or three preregistered $H$: interval buckets of $x$, interval buckets of $x([2]P)+x([3]P)$ (a genuine two-view mixture), and a bucket of the length-$\lceil\log_2B\rceil$ Legendre pattern $\chi(x(P+[j]G))$. Estimate $\varepsilon_\Delta$ by $10^4$–$10^5$ sampled $(n,\delta)$ pairs along a progression (well under 1M events, no training). Threshold $\sqrt{\Delta/q}\approx0.18$ at that size, so sampling error is negligible. A negative excludes only those $H$ at that size; it would, however, record the first exact finite negative for the bucketing conversion itself. Learned $H$ would additionally charge training samples, model size as advice, and fresh-sample $\varepsilon_\Delta$ after model freeze.

## Card 2 — Legendre-PRF key-symmetry attacks do not transfer (scoped negative, new to record)

**Idea tested.** The sequence $s_k(j)=\chi(x(Q+[j]G))$ (or any cheap bit) is a Legendre-PRF-like shift problem: we know a window at unknown shift $k$ and can compute the base sequence anywhere. Could the recent Legendre-PRF key-recovery machinery give a sub-square-root shift finder?

**Prior art actually read.** Beullens–Beyne–Udovenko–Vitto, ePrint 2019/1357 (abstract): time $O(p\log^2p/M^2)$ with $M$ queries. Kaluđerović–Kleinjung–Kostić, ANTS XIV (abstract and §1 read): based on the Möbius group action on degree-$r$ keys; for $r<3$, $O(p^{r/2})$ time with $O(p^{r/4})$ queries, $O(p^r\log p/M^2)$ with $M$ queries; for $r\ge3$, $O(p^{r-3})$ after $O(p^3)$ precomputation.

**Why it fails here, exactly.** (a) The linear case is itself $\Theta(\sqrt p)$ time; the symmetry $L_K(ax+b)=\chi(a)L_{(K+b)/a}(x)$ buys an $M^2$ saving in *queries*, which are free for us (the oracle is public). So even a perfect transfer gives square root. (b) The sub-square-root higher-degree case needs a cheap input action whose induced key action has $p^3$-size orbits. On $E$, the cheap input actions are translations $P\mapsto P+[b]G$ (key action $k\mapsto k+b$, already the random self-reduction used by every generic algorithm) and automorphisms. A multiplicative key action $k\mapsto uk$ requires a cheap map realizing $[u]$ on coordinates; for ordinary $E$ this is an endomorphism of norm $\ge|D|/4\approx p$ unless the CM discriminant is small, i.e. a special curve, and then it is the known $\sqrt{|\mathrm{Aut}|}$ constant. Stride-$a$ windows of the target are windows of the generator $[a]G$, which need a new table per $a$. Hence the transfer collapses to BSGS/kangaroo with compressed keys.

**Falsifier:** none needed; checking $\mathrm{End}(E)$ via the discriminant of the synthetic family confirms the absence of small-norm endomorphisms. **Unsupported assumption rejected:** that a key symmetry exists beyond $\mathrm{Aut}(E)$.

## Card 3 — Galois and $p$-adic "measurements" of a rational point are $k$-blind (scoped negative, elementary)

**(a) Galois/field-of-definition features.** Fibers over $Q$ of any rational map (ℓ-division $[\ell]^{-1}(Q)$, isogeny preimages, torsion translates) equal $R+\ker$ with $R$ a rational point; Frobenius acts on the kernel only, so splitting types, degrees of definition, and orbit structures are translation-invariant and independent of $k$.

**(b) $p$-adic lifts, $q\ne p$.** Prime-to-$p$ torsion lifts uniquely and Galois-equivariantly to $\tilde E(\mathbb Q_p^{\mathrm{unr}})$, so $\langle G\rangle$ lifts to a torsion subgroup on which the formal-group logarithm vanishes identically; any lift-independent $p$-adic invariant of $Q$ is therefore constant. This is why Smart's trace-one method (J. Cryptology 1999 abstract read: linear algorithm when the group order equals $p$) needs $q=p$; Teichmüller-style canonical sections give nothing for ordinary $q\ne p$. Deduplicates and sharpens H003 lift-section, H012 PC4 lifts, and the H020 dual-number/Deuring seeds. Satoh–Araki and Semaev 1998 cited from memory, unverified.

**Falsifier:** none; it is a proof sketch root can check in a few lines.

## Deduplication map (why no further card)

| Family | Status in record | My addition |
|---|---|---|
| Scalar-predicate predictors, coarse bits, posterior ordering | H002 L1/L2, H003, H019 A1, H024 raw A | Card 1 subsumes as few-bucket end; closed for low-degree $H$ by KS bound |
| Multiplicative-character coset identification | H013, H014 | unchanged; $q^{-1/12}$ gap remains, no rationale |
| Sparse-power / implicit relations / list decoding | H017, H018 (finite negative) | none |
| Approximate orbit labels (multiplicative) | H017 card 3 | Card 1 is the additive analogue with explicit ledger |
| Translation-linear coordinates, Koopman, dilations | H020 card 3, H024 raw B | transport lemma closes all heights and isogeny chains |
| Four-list filter / approximate phase | H020 card 2 | Card 1 needs strictly less (local stability) |
| DP-table / start-point learning, walk tuning | H002 L3, BL | not re-proposed |
| $\mathbb F_{p^2}$ translates by twist points | not recorded | one line: $x(Q+R)$, $x(Q-R)$ are conjugate; real/imaginary parts are low-degree $\mathbb F_p$-functions of $Q$, closed by KS |
| Structured-set membership | implicit | shown circular (P2 = interval ECDLP) |

## Honest summary for integration

- No survivor with a positive mathematical rationale in this lens. The constructive content is the exact admission gate $\varepsilon_\Delta\gg\sqrt{\Delta/q}$ and its ledger, which also re-expresses the unreviewed H024 posterior card as the few-bucket case.
- Two closures are new: homomorphic transport (no dilation or isogeny composition escapes the KS bound) and the Legendre-PRF symmetry negative. One elementary closure (Galois/$p$-adic $k$-blindness) consolidates scattered seeds.
- Sources read this pass: Kohel–Shparlinski Theorem 1 and Corollary 1 (author PDF), Beullens et al. 2019/1357 (abstract), Kaluđerović–Kleinjung–Kostić ANTS XIV (abstract, §1), Smart 1999 (abstract). Everything else is memory or prior-wave reads and is labelled as such.
- Recommended next action for root: adopt the Card 1 gate as the standing filter for information/learned proposals; run the optional bounded $\varepsilon_\Delta$ probe only if an exact finite negative for the bucketing conversion is worth recording. Nothing else here justifies an experiment or Lean work.
