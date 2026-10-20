# Arithmetic r100: public report

Status: PREFREEZE. No frozen target, no nominee, no author proof submitted for a gate. No mathematical gate, contribution gate or count is assigned by this round.

Runner: Factory Droid / claude-opus-5-5 / high. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

## Summary

Two directions were developed far enough to locate the unpaid step exactly; neither yielded a nominable theorem this round.

**Direction A (family 024, totients).** The pinned companion's `thm:companion` reduces the asymptotics of the least-preimage count \(N_3(x)\) to the existence of one totient \(d\) with \(\ell(d)>3d\). Section A below gives an exact elementary reduction of that seed condition (radical form, cheap-radical classification in low arity, necessary filters), and records that the divisibility route passes through Ford's open \(k=6\) question, whose negative arm would imply Carmichael's conjecture. The seed itself was not found; a search is unmotivated after the r3 experiments, and the question is Erdős's problem #51 territory (confirmed open by bounded searches, recorded in `search-register.json`).

**Direction B (family 182, prime-arguments power saving).** The pinned prime-arguments paper proves a power saving with polynomial-dependent exponent \(c_h\); its integer companion proves the exponent \(c_k\) uniform in the degree. Section B traces the prime paper's own parameter chain and shows, with an explicit degree-4 family, that the h-dependence is intrinsic to that proof's local normalization: the proof's exponent decays super-exponentially along the family. The degree-uniform prime-arguments statement is unfalsified and unproved; the exact unpaid repair step is stated. This direction was already identified and set aside by the i99 scout (same pin); it is recorded as a located open refinement, not a fresh gap.

Fourteen further families were screened at introduction or catalogue level (`screens.md`). No exhaustion, novelty or priority claim is made anywhere in this packet.

## Direction A: the least-preimage seed at k=3 (family 024)

### A.1 Source anchors (stipulated, read in full)

Source: `preprints/An-asymptotic-formula-for-the-number-of-totients-September-25-2026/build/source/`.

- `statements.tex`, `thm:main`: \(V(x)\sim \frac{x}{\log x}G_mA(1;\theta)\) with an explicit finite-arithmetic coefficient; \(V(cx)/V(x)\to c\).
- `statements.tex`, `thm:companion}: for fixed \(k\ge1\), \(N_k(x)=\#\{v\in\mathcal V:v\le x,\ kx<\ell(v)\le(k+1)x\}\) satisfies \(N_k(x)=\frac{x}{\log x}G_m(A(f_k;\theta)+o(1))\), and (i) if some totient \(d\) has \(\ell(d)>kd\) then \(\inf_s A(f_k;s)>0\) and \(N_k(x)\asymp_k V(x)\); (ii) else \(N_k(x)=0\) identically. "The first alternative holds for \(k=1,2\)." The theorem text adds: whether (i) holds for every \(k\) is equivalent to unboundedness of \(\ell(d)/d\), which the weighted formula does not settle.
- `companion.tex`, `lem:fiber-propagation` (Ford's inverse-fiber propagation: a seed \(d\) propagates to \(\gg_\varepsilon d^{-1-\varepsilon}V(x)\) totients with fiber exactly \(\{bd_i\}\)); `lem:ratio-tightness`; `rem:least-preimage-scope`: the \(k=2\) seed is Ford's \(d=2^{18}\cdot257\), all of whose preimages are divisible by \(8\); "We do not determine all integers \(k\) for which the positive alternative occurs."
- Project history: the r52/r53 chain froze and proved a different family-024 target (T024W52, the moving-window asymptotic; proof review found one required erratum, `t024w-proof-r1/report.md`, history copy). That chain never read the companion's least-preimage section (its reading limits state `companion.tex` not read). The full unboundedness target \(\sup_d\ell(d)/d=\infty\) (Erdős #51) was attempted by totient-recovery r3 and left UNRESOLVED with an exact barrier (`totient-recovery-r3-checkpoint.md`, history copy).

So the unpaid source-flagged statement is exactly: **(SEED3) there exists a totient \(d\) with \(\ell(d)>3d\).** By `thm:companion`, SEED3 is equivalent to \(N_3(x)\asymp V(x)\); and \((\forall k\ \mathrm{SEED}_k)\) is Erdős #51.

### A.2 Exact elementary reductions (author; checked)

Write \(g(S)=\prod_{p\in S}\frac{p}{p-1}\) for a finite set of primes, and \(\mathrm{rad}(n)\) for the radical. Since \(n/\varphi(n)=g(\mathrm{rad}(n))\):

**Lemma A1 (radical form).** For a totient \(d\), \(\ell(d)>3d\) iff the least preimage \(n_0\) satisfies \(g(\mathrm{rad}(n_0))>3\). A preimage whose radical \(S\) has \(g(S)\le3\) is called *cheap*; any cheap preimage kills SEED3 for its \(d\).

**Lemma A2 (cheap radicals, low arity).** (i) Every singleton and every pair is cheap; \(g(\{2,3\})=3\) exactly. (ii) A triple \(S\) is expensive iff \(\{2,3\}\subseteq S\) (then \(g(S)=3q/(q-1)>3\)); every triple omitting \(3\) is cheap, the maximum being \(g(\{2,5,7\})=35/12<3\). (iii) At arity four the boundary is genuinely delicate: \(g(\{2,5,7,31\})=\frac{35}{12}\cdot\frac{31}{30}=\frac{1085}{360}>3\) but \(g(\{2,5,7,37\})=\frac{35}{12}\cdot\frac{37}{36}=\frac{1295}{432}<3\).

*Proof.* Direct evaluation of \(g\); monotonicity \(g(S\cup\{q\})=g(S)\cdot q/(q-1)\) decreasing in \(q\). ∎

**Lemma A3 (necessary filters).** If \(\ell(d)>3d\) then: (i) \(d+1\) is composite (else \(n=d+1\) is a preimage of ratio \(1+1/d\)); (ii) \(d\) is not a prime-power totient value \(p^{e-1}(p-1)\); (iii) \(d\) is not of the form \(2^A3^B\) with \(A\ge1\): then \(n=2^A3^{B+1}\) has \(\varphi(n)=2^A3^B=d\) and ratio exactly \(3\); (iv) \(d\neq2^{a-1}q^{b-1}(q-1)=\varphi(2^aq^b)\) for any odd prime \(q\) and \(a,b\ge1\) (ratio \(2q/(q-1)\le3\)). Each filter excludes an explicit thin family; all are checkable at negligible cost in any search.

**Lemma A4 (the divisibility route is blocked by Ford's open case).** If a totient \(d\) has every preimage divisible by \(42\) (respectively \(30\)), then \(\ell(d)\ge\frac72\,d\) (resp. \(\frac{15}{4}d\)), hence SEED3. But any such \(d\) has every preimage divisible by \(6\), which is Ford's open question: his Section 7.3 search found totients whose preimages are all divisible by each \(k\le11\) **except \(k\in\{6,10\}\)** (\(d=2^{18}\cdot257\) for \(k\in\{2,4,8\}\); \(d=54\) for \(k\in\{3,9\}\); \(d=12500\) for \(5\); \(d=294\) for \(7\); \(d=110\) for \(11\)), and records: "It appears that there might not be any totient, all of whose pre-images are divisible by 6, but I cannot prove this." (Verified verbatim this round in r2's retained text extraction of Ford's paper, arXiv:1104.3264 lineage; see `reading-limits.md`.) Ford adds the reverse hardness: "Any totient with a unique pre-image must have that pre-image divisible by 6, so the non-existence of such numbers implies Carmichael's Conjecture." So disproving common divisibility by 6 would prove Carmichael's conjecture; the divisibility route to SEED3 is blocked from both directions.

**Lemma A5 (SEED3 is strictly weaker than divisibility).** SEED3 does not require any common divisor: a totient whose fiber's radicals all avoid the cheap list, e.g. all contain \(\{2,5,7,11\}\) (\(g=3.208\ldots\)) or are odd with the first eight odd primes (\(g=3.056\ldots\)), satisfies SEED3 without \(6\mid n\). Neither Ford's question nor its negation settles SEED3.

**Lemma A6 (r3's exact barrier, restated).** For every totient \(d\) and preimage \(n\), \(\log(n/d)=\sum_{p\mid n}\log(1+\frac1{p-1})\le\sum_{p\mid n}\frac1{p-1}\le\sum_{u\mid d}\frac1u=\sigma(d)/d\), using the injection \(p\mapsto p-1\) from \(\mathrm{supp}(n)\) into the divisors of \(d\). Hence over any fixed support \(S\supseteq\mathrm{rad}(d)\), \(\ell(d)/d\le\exp\prod_{q\in S}(1-\frac1q)^{-1}\), uniformly in the exponents. (This is §2 of `totient-recovery-r3-checkpoint.md`; the proof is reproduced here exactly.) Consequences: unbounded ratio (Erdős #51) needs growing support; but SEED3 is **not** excluded at fixed support (\(\{2,3,5\}\) allows up to \(e^{15/4}\)). The obstruction to SEED3 is the least-preimage phenomenon (Lemma A3), not this bound.

### A.3 What was tried

r3's completed finite run (129 totients: the box \(2^a3^b5^c\), five Ford examples, primorial values \(\varphi(P^e)\)) found maximum ratio \(257/128=2.0078\ldots\) (Ford's record, reproduced) and exhibited the \(d+1\)-prime obstruction killing primorial constructions. This round added no new search: with no construction principle beyond Ford's Section 5 mechanism (which the companion already uses as `lem:fiber-propagation`, and whose gain is the factor \(b/\varphi(b)\) on propagated fibers), and with Ford's own suspicion that even common divisibility by 6 never occurs, a bounded brute-force hunt has no positive expectation. Four bounded web searches (`search-register.json`) located no known totient with all preimages divisible by 6, no improvement of the \(257/128\) record, and Erdős #51 still listed open (erdosproblems.com, page edited April 2026).

### A.4 Why nothing was frozen

A conditional statement "SEED3 implies \(N_3(x)\asymp V(x)\)" is the source's `thm:companion`(i) itself: restating it adds nothing. The unconditional content is exactly SEED3, open in effect since Ford (1998), Carmichael-hard in the negative for the divisibility sub-route, and beyond a justified search this round. Lemmas A1–A6 are elementary reductions and are recorded as screens, not as substantial results.

## Direction B: degree-only exponent at prime arguments? (family 182)

### B.1 The two pinned theorems (stipulated)

- Integer paper `.../A-power-saving-for-intersective-.../sections/introduction.tex`, `thm:main`: for every \(k\ge2\) there is \(c_k\in(0,1)\) such that every intersective \(h\) of degree \(k\) with positive leading coefficient admits \(C_h,N_h\) with \(|A|\le C_hN^{1-c_k}\) for \(A\subseteq[N]\) avoiding \(h(\mathbb N_+)\). **Exponent common to all polynomials of degree \(k\).**
- Prime paper `.../A-Power-Saving-for-Polynomial-Differences-at-Prime-Arguments-.../sections/introduction.tex`, `thm:main`: for prime-intersective \(h\) (unit root modulo every modulus), \(\deg h\ge2\), positive leading coefficient, \(|A|\le C_hN^{1-c_h}\) for \(A\) avoiding \(\{h(p)\}\), with **both** constants polynomial-dependent.

The flagged refinement: **(DEG) the prime-arguments bound holds with an exponent \(c_k\) depending only on \(\deg h\)** (\(C_h,N_h\) unrestricted). The i99 scout (same pin; history copy) recorded DEG explicitly: the stronger height-free variant (\(C_k,N_k\) too) is *falsified* by \(h_H(t)=H(t-1)^k\), all of whose nonzero prime values exceed \(H\); and for DEG itself: "not falsified; a normalization/prime-progression adaptation would need accounting, and no substantiality claim is made for such an extraction." i99 did not pursue it.

### B.2 Where the prime paper's exponent loses degree-uniformity (verified chain)

All labels are the prime paper's; the files `local.tex`, `tuples.tex` (parameter parts), `descent.tex` were read (extents in `reading-limits.md`).

1. `local.tex`, `eq:local-exponents`: \(\delta=\frac{1}{100k2^k}\), \(\gamma=\delta/10\) — degree-only. But `lem:local-sums` needs a threshold \(P_1\) such that for every \(l\ge1\) and \(p\ge P_1\), \(F=h_l\bmod p\) is nonconstant (uniformly in \(l\)) and the allowed-regular class is large; and `lem:auxiliary`'s last clause makes \(b_{m_p,p}\) a unit only past an h-dependent threshold (resultants/discriminants of the factorization of \(h\)). For \(p<P_1\), `lem:local-lifting` produces exponents \(S_p(h,p)\ge0\), \(E_p=2S_p+1\).
2. `local.tex`, `lem:admissible-cycle`: the cycle length \(L\) must satisfy \(4\delta L>2\) **and** \(p^{E_p}\mid L\) for every \(p<P_1\). Hence \(L\ge\prod_{p<P_1}p^{E_p}\).
3. `tuples.tex`: \(t\) with \((t+1)\delta/2>5\) is degree-only; but \(K=L!\), \(d=|V|=K^{2t+1}\), and `eq:small-prime-modulus`: \(M_0=\prod_{p<P}p^{E_p}\) with \(P>P_1\).
4. `descent.tex`: the good-assignment proportion is \(\rho_l\ge\rho_*=M_0^{1-L}\) (`eq:good-proportion`); the uniform induction (`prop:uniform-descent`) requires \(s_0=ka_0+2a_0/\zeta\) with \(\theta_0=M_0^{s_0}(1-3\rho_*/4)<1\), forcing \(s_0\log M_0<\frac34\rho_*+O(\rho_*^2)\); and the final exponent is \(c_h=a_0/d\).

So the exponent this proof delivers satisfies
\[
 c_h\;=\;\frac{a_0}{d}\;\le\;\frac{M_0^{\,1-L}}{k\,(L!)^{2t+1}\,\log M_0}\,(1+o(1)),
\]
with \(M_0\) and \(L\) built from the h-dependent data \(P_1,\{E_p\}\).

### B.3 An explicit degree-4 family driving the proof's exponent to zero (author; checked)

For an odd prime \(q\) put
\[
 h^{(q)}(x)=q(x-1)^2+q(x-1)^3+(x-1)^4 .
\]
Then: \(\deg h^{(q)}=4\); leading coefficient \(1>0\); content \(1\); \(h^{(q)}(1)=0\), so \(r=1\) is a unit root modulo every modulus and \(h^{(q)}\) is prime-intersective. At \(p=q\): \(\mathfrak z_q=1\), and \(h^{(q)}(1+X)=qX^2+qX^3+X^4\), so \(m_q=2\) and \(b_{m_q,q}=q\equiv0\pmod q\). Compute the auxiliary polynomial at \(l=q\): \(r_q=1-q\), \(T_q(x)=1+q(x-1)\), \(\lambda(q)=q^2\), and
\[
 h_q(x)=\frac{h^{(q)}(1+q(x-1))}{q^2}
      =q(x-1)^2+q^2(x-1)^3+q^2(x-1)^4\;\equiv\;0\pmod q
\]
as polynomials. Hence the nonconstancy-uniformly-in-\(l\) required at every \(p\ge P_1\) fails at \(p=q\), forcing \(P_1>q\), hence \(q^{E_q}\mid L\) with \(E_q\ge1\), so \(L\ge q\) and \(M_0\ge q\). By the chain of §B.2, the exponent delivered by this proof along \(\{h^{(q)}\}\) decays faster than \(q^{-(1-o(1))q}\) while the degree stays \(4\).

So the h-dependence of \(c_h\) is intrinsic to the paper's parameter scheme; DEG cannot be extracted from this proof by bookkeeping alone. (This says nothing about the truth of DEG; no lower bound on avoiding sets for \(h^{(q)}\) is known to me. The multiples of \(q\) avoid every value \(h^{(q)}(p)\) with \(p\not\equiv1\pmod q\) only, which gives no clean large avoiding set.)

### B.4 The exact unpaid step

The degeneration pattern is: for \(p\mid l\) with \(p\mid b_{m_p,p}\), the auxiliary polynomial satisfies \(h_l\equiv0\pmod p\), i.e. \(p\mid\mathrm{cont}(h_l)\). A candidate repair is to renormalize the auxiliary family by content, \(\bar h_l=h_l/\mathrm{cont}(h_l)\), keeping the progression maps \(T_l\). The source's propagation identity \(h_l(Dx-i)=\lambda(D)h_{lD}(x)\) then reads \(\bar h_l(Dx-i)=\bigl(\lambda(D)\,\mathrm{cont}(h_{lD})/\mathrm{cont}(h_l)\bigr)\bar h_{lD}(x)\), so closure of the renormalized family under progression restriction requires
\[
 \mathrm{cont}(h_l)\ \mid\ \lambda(D)\,\mathrm{cont}(h_{lD})\qquad\text{for all }l,D,
\]
together with an avoidance-transport argument for the renormalized values. Neither the divisibility nor a counterexample to it was established. Separately untreated: degeneration of \(\bar h_l\bmod p\) to a *nonzero* constant (all values coprime to \(p\)), where within-class differences become automatically allowed and the progression argument changes character. Finally, how the *integer* paper achieves degree-uniformity was not examined this round (only its introduction was read); whether its normalization already contains the repair is unknown here. These are the unpaid items; consistent with i99's note, no substantiality claim is made for the extraction even if the repair succeeds, and the direction's prior screening by i99 is disclosed.

### B.5 Why nothing was frozen

DEG's proof requires the unpaid repair of B.4 plus re-verification of the tuple/lift/kernel/descent chain under the renormalized family — a multi-section derivation with an open integrality step at its base, not completable this round at author-proof standard. The observation of §B.3 is elementary and proves a property of a proof, not a theorem. Not frozen.

## Novelty limits

Nothing in this packet is claimed new to the literature. Lemmas A1–A6 are elementary; A6 is r3's. §B.2–B.3 are a parameter audit of the pinned proof with an explicit example; the underlying phenomenon (degeneration of Lucier–Rice auxiliary polynomials at bad primes) is the reason the small-prime treatment exists in both papers. Bounded searches (four queries) are navigation-grade only and are recorded in `search-register.json`; citations seen but not acquired are in `external-navigation.json`. "New to this project" is not asserted either: i99 had already isolated DEG, and r3 had already isolated the SEED barrier.
