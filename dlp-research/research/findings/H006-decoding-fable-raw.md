# H006 decoding review: raw Factory Fable report

Unaccepted raw review. Root found a counterexample to its universal no-constant-success assertion and its distinct/iid yield wording; see H006-decoding-disposition.md. Retaining a report does not endorse its lower bounds or novelty claims. No experiments were run.

# Review of H006 raw report, Mechanisms B and C (read-only)

**Verdict.** Both mechanisms are correctly rejected, but for partly different reasons than the raw gives. B's yield formula is right (and is an equality, not a bound); its conclusion is right and in fact stronger than stated: no admissible parameter choice gives constant per-call success, and the full repetition-inclusive work is about $p$, not $\sqrt p$. C fails at the construction level: translation does not preserve the code space, so no Guruswami-style folded elliptic code exists for it; the raw's "whole orbits" premise and its "cost exceeds $p$" estimate are both wrong as stated, though the mechanism still loses. Best supported baseline: generic square root with the known automorphism constant. Verified improvement: **NONE**. I ran no experiments, made no edits, launched no children. The only file I wrote was a text extraction of the GS99 PDF in `/tmp`, outside the repo.

## Sources inspected this session

- Guruswami–Sudan 1999, journal version: https://people.csail.mit.edu/madhu/papers/1998/venkat-journ.pdf (Lemma 26, Theorem 27, Proposition 22).
- Guruswami 2008/2010, folded codes from Artin–Frobenius automorphisms: https://arxiv.org/abs/0811.4139 (full HTML; Prop. 2.2, §3, §5.5–5.6, Lemmas 5.7–5.8).
- Guruswami–Xing 2012, folded codes from function-field towers: https://arxiv.org/abs/1204.4209 (full PDF; §1.1, §1.2, §3 "A useful automorphism").
- Cheng 2005, Hard Problems of AG Codes: https://arxiv.org/abs/cs/0507026 (full HTML; §2 properties 1–3, Lemma 3, Theorems 1–3).
- Cheng–Wan RS decodability / DLP: https://epubs.siam.org/doi/10.1137/S0097539705447335 (abstract only; not needed for any conclusion).

Not inspected: Guruswami–Rudra 2008, Guruswami–Wang 2011 linear-algebraic decoder, later folded-RS list-size improvements. Where I use them below I say so.

## Mechanism B: GS interpolation as a batched minor finder

**Radius check (confirmed).** GS99 Theorem 27 decodes a one-point AG code with message space "pole order $\le k+g-1$ at $x_0$" whenever $t^2 > (k+g-1)n$. For an elliptic curve $g=1$ and $L(dO)$ has dimension $d$ (Cheng §2 property 3), so the message space is exactly $L(dO)$ with $k+g-1=d$. The raw's condition $N < (d+e)^2/d$ is exactly GS99 Lemma 26. The decoder returns every $f\in L(dO)$ with agreement $\ge t$ (Lemma 24), with cost at least $\Omega(N t^2)$ field operations (Prop. 22), so the per-call lower bound $N$ I use below is generous to the attacker.

**Yield formula (confirmed, and it is an equality).** Let the $N$ evaluation points be distinct nonzero points of $\langle P\rangle$ with i.i.d. uniform multipliers (mixing $P$-type and $Q$-type as in Mechanism A), and let $g$ be uniform on $L((d+e)O)\setminus L(dO)$, independent of the multipliers. A "useful" output is $f\in L(dO)$ with $g-f$ vanishing on exactly $d+e$ evaluation points. Then

$$\mathbb E[\#\text{useful}] \;=\; \binom{N}{d+e}\cdot\frac1p\cdot\frac{q-1}{q^e-1}.$$

Proof: for a $(d+e)$-subset $T$, $\sum_T=O$ has probability exactly $1/p$ (a nonzero linear form in uniform $\mathbb Z/p$ variables). Given that, there is $h_T\in L((d+e)O)$ with zero divisor exactly $T$, unique up to scalar, and $h_T\notin L(dO)$. $g-f=ch_T$ for some $f\in L(dO)$ iff the class of $g$ in the $e$-dimensional quotient $L((d+e)O)/L(dO)$ is a nonzero multiple of $[h_T]$: $(q-1)$ of the $(q^e-1)$ nonzero classes. Different $T$ cannot share an $f$ since $g-f$ has at most $d+e$ zeros. Agreement strictly between $d$ and $d+e$ is useless: the missing zeros are rational points with unknown logs. This is the lineage of Cheng's Lemma 3 (whose received word has its extra pole at $Q$, target sum $Q$; the raw puts the extra pole at $O$ and targets $O$. Both work and give the same factor.)

**Field size vs subgroup order.** The $1/p$ is the subgroup order $p=\operatorname{ord}P$; the $(q-1)/(q^e-1)$ is the field size $q$, because the quotient is an $\mathbb F_q$-space. They are tied only by Hasse, $p\le q+1+2\sqrt q$, and by the constraint the raw omits: $N\le p-1$, since all evaluation points lie in $\langle P\rangle\setminus\{O\}$. That constraint matters below.

**Euler's $e$ vs integer $e$.** In the raw's inequality $(1+u)\ln\!\big(e(1+u)/u\big)\ge\ln q$, the $e$ inside the log is Euler's number (from $\binom Nw\le(eN/w)^w$) while $u=e/d$ uses the integer. The inequality itself is a correct necessary condition (derived by bounding $\binom{N}{w}$ with $w<Ne/t$ and $N<d(1+u)^2$). But the raw's reading of its $u\ge1$ branch is not supported: for large $u$ the left side is about $1+u$, so the inequality only gives $u\gtrsim\ln q$, not $u\gtrsim q/e$. The stronger statement is true but needs a different argument, which also gives a cleaner result.

**Correct necessary condition.** Write $t=d+e$, $w=N-t$, $\rho=t/N$. GS requires $e>t w/N=N\rho(1-\rho)$. Constant per-call success ($\mathbb E\ge1$) requires $\binom Nt\ge p\,q^{e-1}$, hence with $\binom Nt\le2^{NH(\rho)}$:

$$N\big[H(\rho)-\rho(1-\rho)\log_2 q\big]\;\ge\;\log_2(p/q)\;\approx\;0 .$$

Since $H(\rho)\le\rho\log_2(e/\rho)$ (Euler's $e$) and symmetrically in $1-\rho$, the bracket is nonnegative only when $\rho\lesssim e/q$ or $1-\rho\lesssim e/q$. Using $N\le p<2q$: the first case forces $t=\rho N\le2$, so $d=e=1$ and GS forces $N\le3$; the second forces $w\le2$, and then $\mathbb E\ge1$ needs $N\ge p$ (for $w=1$) or $N\ge\sqrt{2pq}>p$ (for $w=2$), both violating $N\le p-1$. So for $q\gtrsim2^{10}$, **constant per-call success is impossible for every admissible $(N,d,e)$**, not merely expensive. The raw's "$N=\Omega(q)$" is the right direction but understates it; under the paper's cofactor-2 assumption ($p\approx q/2$) even $N\approx0.74q$ would already exceed the point supply.

**Repetitions.** With $\mathbb E<1$, expected calls $\ge1/\mathbb E$ and total work $W\ge N/\mathbb E = N\,p\,q^{e-1}/\binom Nt$. Regime by regime, using only the GS constraint and $N\le p$:
- $w=1$: $W\ge p$. $w=2$: $e\ge2$, $W\ge 2pq/(N-1)\ge2p$. $w=3$: $e\ge3$, $W\ge6pq^2/N^2\ge6p$.
- $4\le w<\sqrt N$: $e\ge w$, $W\ge p\cdot w!\,(q/N)^{w-1}\gtrsim p\,w!$.
- $w\ge\sqrt N$ or $t\le N/2$: the entropy bracket is positive and $W\ge p\cdot2^{\Omega(\sqrt N\log q)}$ or $p\cdot2^{\Omega(\log^2 q)}$.
- Tiny $N<16$: $W\ge Np/2^{N}>p/2^{15}$.

So the honest full-work accounting for B is $W\gtrsim p$ in every nontrivial regime, worse than $\sqrt p$ by a factor $\gtrsim\sqrt p$. The raw's "at least $q$" is correct in substance. The "unsupported assumption" the raw names (decoding beyond the Johnson radius at agreement $\approx d+1$) is indeed the only exit, and it is the §6 gap itself.

Minor corrections to the raw text: the displayed yield is "$=$", not "$\le$" (it is "$\le$" only as a bound on what GS returns); add $N\le p-1$; replace the $u\ge1$ sentence with the entropy argument.

## Mechanism C: codes folded along translation orbits

**Construction-level failure (primary sources).** Folding needs an automorphism $\sigma$ of the function field that (i) preserves the message space and (ii) carries a low-degree algebraic relation. In Guruswami 0811.4139, the message space is $\mathcal L(\ell M')$ where $M'$ is the unique place above the totally ramified $M$ (Prop. 2.2(i)), so every Galois element fixes it, and the relation is the Artin–Frobenius congruence $\sigma_A(f)\equiv f^{q^D}\pmod{A'}$ at an inert place (Lemma 5.8(ii), with $Db>\ell d$ so $f$ is determined by its residue, Lemma 5.7). In Guruswami–Xing 1204.4209 §3, $\sigma:x_i\mapsto\gamma^{(r+1)^{i-1}}x_i$ "keeps $P_0$ and $P_\infty$ unchanged" and acts diagonally on the local expansion at the fixed point $P_0$; §1.1 states explicitly that such a $\sigma$ "is only known (or even possible) for very special function fields."

Translation $\tau_T:P\mapsto P+T$ on $E$ violates (i): $(f\circ\tau_T)$ has its pole where $P+T=O$, so $\tau_T^*L(dO)=L(d\cdot(-T))$, and $L(dO)\cap L(d(-T))$ is just the constants. The code space is not invariant; it is moved almost entirely. A divisor invariant under $\tau_T$ must be constant on $\langle T\rangle$-cosets, so on a prime-order curve any nonzero effective invariant divisor has degree $\ge p>N$, giving the trivial full-space code. And $\tau_T$ has no fixed point at all, so neither the Artin–Frobenius device nor the diagonal-local-expansion device has an anchor. There is no folded elliptic code along translation in the sense of either primary source.

**Orbits vs blocks.** On prime-order $E(\mathbb F_q)$, the $\langle\tau_T\rangle$-orbit of any point is a full coset of $\langle T\rangle=E(\mathbb F_q)$, size $p$ (not $q$). The raw's "orbits" of length $F$ are partial blocks, segments of one orbit. The raw's claim "zero sets must be unions of whole orbits" is therefore wrong as stated. The correct statement: a folded decoder only counts fully agreeing blocks, so a useful zero set must *contain* at least $(R+\varepsilon)N'$ full blocks ($N'=N/F$ blocks, $R=d/N$), and separately all $d+e$ zeros must be evaluation points (else unknown logs). It need not be a union of blocks, so the raw's candidate count $\binom{N/F}{(d+e)/F}$ undercounts. The correction does not help: full-block agreement already forces $e\ge\varepsilon N$, and the class factor $q^{-(e-1)}$ from B is decoder-independent.

**What honest folding on $E$ gives.** The automorphisms of $E$ that fix $O$ (hence preserve $L(dO)$) are $\operatorname{Aut}(E,O)=\{\pm1\}$ for an ordinary curve with $j\ne0,1728$ (order 4 or 6 at $j=1728,0$). Folding by $[-1]$ pairs $P$ with $-P$: that is the negation map, i.e. exactly the known $\sqrt{|\operatorname{Aut}|}$ constants the loop already treats as the reference. Frobenius-folding over $E(\mathbb F_{q^m})$ is the real GX analogue but produces blocks $(f(P),f(P)^q,\dots)$ that carry no new information and involve points with unknown logs; irrelevant for prime-field targets.

**The raw's cost estimate is not established.** "Either way the cost exceeds $p$" is conditional on a decoder that does not exist and on an unstated cost model. Correct scoping: the rejection is construction-level; any cost statement must be conditional. For the record, granting an idealized GR/GW-type decoder (radius $\frac{s}{s+1}(1-\frac{mR}{m-s+1})$, so $\varepsilon\ge1/(s+1)$, cost $\ge N^{s-1}$ or $q^{s-1}$ per call, from Guruswami–Xing §1.1's summary of GR08/Gur11, not inspected directly): the yield-$\ge1$ regime needs $e\le1+(N-\log_2p)/\log_2 q$ and $e\ge N/(s+1)$, hence $s\gtrsim\log_2 q$ and $N\gtrsim\log_2 q$, so $W\ge N^{s-1}\gtrsim q^{\log_2\log_2 q}\gg\sqrt p$; the yield-$<1$ regime gives $W\gtrsim p$ or $2^{\log_2 q\cdot\log_2 N}$. If instead a decoder cost poly$(N,1/\varepsilon)$ were available, $N\approx\log_2^2 q$, $e\approx\tfrac12\log_2 q$ would give yield $\ge1$ and a quasi-polynomial ECDLP. That is a reductio, not a bridge: such a decoder is the §6 gap restated.

## Surviving constructive bridge (precise, cheap to kill)

One variant is not covered by any primary source and is not circular on its face: a **shifted-space difference-equation decoder**. Interpolate $Q=A_0+\sum_{i=1}^{s}A_iY_i$ with $Y_i$ standing for $f(P+(i-1)T)$, i.e. $\tau_T^{(i-1)*}f\in L(d\cdot(-(i-1)T))$, so the identity $A_0+\sum_i A_i\,\tau_T^{(i-1)*}f=0$ is well typed in the function field and is $\mathbb F_q$-linear in $f$. For this to beat Johnson it needs:

- **A1 (unproven):** the solution set in $L(dO)$ is an affine space of dimension $\le s-1$. For $s=2$ this holds: two solutions have a $\tau_T$-invariant ratio, which is pulled back from $E/\langle T\rangle$ and has a divisor of degree $<p$ supported on $<p$ points, hence constant. For $s\ge3$ the GX proof does not transfer (no fixed point, no eigenbasis), and I have no replacement.
- **A2 (cost):** pruning the affine space to a useful $f$ is finding $\lambda\in\mathbb F_q^{s-1}$ lying on $\ge d+e$ of $N$ given hyperplanes, i.e. decoding a random $[N,s-1]_q$ code at error fraction about $1/2$. In the only regime where yield $\ge1$ ($s\gtrsim\log_2 q$, $N\gtrsim\log_2^2 q$), generic information-set decoding succeeds per trial with probability about $2^{-(s-1)}\approx1/q$, so total work $\gtrsim q$ unless the pruning has algebraic structure. Subspace-evasive pre-coding (GX's fix) is unavailable because $f$ is dictated by the instance, not chosen.

**Cheap falsifier (proposed only, not run):** on a 10–14-bit prime-order curve, for $s=3,4$ and $m\approx s^2$, interpolate $A_i$ for random $g$ and compute $\dim$ of the solution space in $L(dO)$. If it is typically $\gg s-1$, A1 dies and C is closed. If it is $\le s-1$, count useful elements against the B yield formula and time the pruning; the prediction from A2 is cost $\approx q$ per useful relation. Either outcome leaves $\sqrt p$ unbeaten; the experiment only decides whether the variant is worth a line in the register.

## Bottom line for root

- Best supported complexity: generic $\Theta(\sqrt p)$ with the known automorphism constant. Verified improvement: **NONE**.
- B: yield formula exact as stated above; constant per-call success impossible for all admissible parameters at $q\gtrsim2^{10}$; repetition-inclusive work $\gtrsim p$. Fix the $u\ge1$ step, add $N\le p-1$, change "$\le$" to "$=$".
- C: reject at construction level (code space not translation-invariant; no fixed place for Artin–Frobenius or diagonal local expansion). Replace "whole orbits" with "contains enough full blocks"; drop "cost exceeds $p$" or make it conditional as above. Honest folding on $E$ reproduces only the known $\pm1$ (or $j=0,1728$) constants.
- The one non-circular residue is the shifted-space difference-equation decoder with assumptions A1/A2 and the toy-curve dimension check as its falsifier. Nothing here changes the §6 gap: decoding elliptic codes at agreement $d+1$ in $o(\sqrt q)$ remains equivalent to the problem itself.
