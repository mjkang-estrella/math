# H045 raw Factory Opus public-signal report — UNACCEPTED

2026-10-09 UTC. Provider acpRegistry_factory_droid / claude-opus-5-5.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h045-public-signal-factory-opus-20261009-r1`.
Terminal task_status completed, no pending child runs. Claims below require
independent mathematical, source and cost review. Provider usage footer is
unverified metadata, not ECDLP work or measured research cost.

# H045 nonlinear-signal lens: findings

I found no construction that changes the complexity or complete-work estimate. The best supported exponent is still 1/2, and verified improvement over the baseline is still NONE.

I could not build a public point observable that meets the H044 premise, which is a known chirp with correlation $\varepsilon=q^{-\gamma}$ and $\gamma<1/22$. I did get three scoped results that root could use:
- **Ceilings for the two canonical recurrences.** Every bounded-L1 post-processing of the Miller/Rück coefficient and of the EDS σ-normalization has chirp correlation at most $O(q^{-1/4})$ and $O(q^{-1/8})$ respectively. Both are far above the decoder threshold, so both classes are closed for this decoder.
- **An exact Legendre bit of the DL.** It comes from an elliptic Gauss lemma. Evaluating it is the hard part, and even a free oracle only reduces the problem to Legendre-PRF key recovery, which is about $\sqrt q$ by known attacks.
- **A structural reason** why elliptic recurrences over $\mathbb F_p$ do not produce mod-$q$ quadratic phases.

This was read-only work. There were no scripts, runs, spectrum scans, edits or children. The only arithmetic was a hand check on $q=13$, marked below.

## A. Miller/Rück coefficient: a first-order additive cocycle, closed at $q^{-1/4}$

- **Observable.** Let $b(Q)=a_Q/q\in\mathbb F_p$, where $a_Q$ is the H027 Miller coefficient, computable in $O(\log q)$ group operations. The observable is $F(n)=\Phi(b(nG))$ for any $\Phi:\mathbb F_p\to\mathbb C$ with additive-Fourier L1 norm $L$.
- **Mechanism.** H027's defect law gives $b(P+T)=b(P)+b(T)-\lambda(P,T)$. For fixed $T$, the chord/tangent slope $\lambda(\cdot,T)$ is a degree-2 rational function with simple poles at $O$ and $-T$. Because the pole order is 1, it cannot have Artin–Schreier form. The function $b$ is also the unique solution of this relation, since $\mathrm{Hom}(\mathbb Z/q,\mathbb F_p)=0$. So $b$ is the finite-field analogue of the Weierstrass ζ-function.
- **Bound (my derivation).** Apply the H044 differencing identity once. Each inner sum is a mixed sum of $\psi(t\lambda(P,T))$ against a group character, which Kohel–Shparlinski bounds by $4\sqrt p$, plus at most 2 exceptional points. This gives

  $$|S_F(\alpha,\beta)|\le L\left(\frac{4\sqrt p+3}{q}\right)^{1/2}\approx 2L\,q^{-1/4}$$

  for every $\alpha,\beta$, and the same bound for linear coefficients.
- **Consequence.** The decoder fails whenever $L\le q^{9/44-o(1)}$. Adding any low-degree rational term inside ψ keeps the bound.
- **Not covered.** Multiplicative characters and bit-level functions of $b$. Being outside the bound is not evidence of a signal.
- **Falsifier.** A reviewer checks the cocycle sign, the divisor of the slope function and the mixed-sum hypotheses.

## B. EDS σ-normalization $\varphi$: a second-order cocycle, closed at $q^{-1/8}$

This answers the n² versus k² question directly.

- **Observable.** $F(n)=\Phi(\varphi(nG))$, where $\varphi$ is the H002 pointwise normalization (polylog to compute) and $\Phi=\sum_\chi c_\chi\chi$ is a combination of characters of $\mathbb F_p^*$ of any order $m\mid p-1$.
  - For $m=2$, H003 already shows $\chi\circ\varphi$ is rational.
  - For $m\ge3$ it is not, so this is the case the archive had not covered.
- **Addition law (derived from the classical identity $x(nP)-x(mP)=\psi_{m+n}\psi_{m-n}/(\psi_m^2\psi_n^2)$).** Using $\varphi(nG)=\gamma^{n^2}W_G(n)$, the $\gamma$-exponents cancel by the parallelogram law, giving

  $$\varphi(P+T)\varphi(P-T)=\varphi(P)^2\varphi(T)^2\,(x(T)-x(P)).$$

  Hence for nonzero $h_1,h_2$, with $M=(h_1+h_2)/2$ and $D=(h_1-h_2)/2$:

  $$\frac{\varphi(P+h_1+h_2)\varphi(P)}{\varphi(P+h_1)\varphi(P+h_2)}=\frac{\varphi(M)^2}{\varphi(D)^2}\cdot\frac{x(M)-x(P+M)}{x(D)-x(P+M)}.$$

  The degenerate cases $h_1=h_2$ and $h_1=-h_2$ also give degree-2 functions. Each has a simple zero or pole, so it is not an $m$-th power for any $m\ge 2$.
- **Bound.** Two differencing steps and the Chen / Shparlinski–Stange mixed bound ($4\sqrt p$) give

  $$|S_F|\le L(\sqrt2+o(1))\,q^{-1/8}.$$

  This also holds for products with the observable from A.
- **Why the n² does not help.** In EDS the $n^2$ sits on $\gamma\in\mathbb F_p^*$, whose order divides $p-1$ and is coprime to $q$. The "bilinear" part of the double difference, $\varphi(M)^2/\varphi(D)^2$, therefore cannot be $e_q(2\alpha h_1h_2)$. What remains depends on $P$ through a nonconstant degree-2 rational function, and the Weil bound kills it.
  - A real chirp needs a nondegenerate $\mu_q$-valued bilinear form, which means a Weil or Tate pairing in $\mathbb F_{p^e}$ with $e=\mathrm{ord}_q(p)$. That is excluded.
- **Depth heuristic.** The same differencing argument gives exponent $2^{-(s+1)}$ for depth-$s$ cocycles. Escaping $1/22$ would need depth at least 4. Theta/σ quasi-periodicity stops at depth 2, and I know of no deeper cheap elliptic object.

## C. Elliptic Gauss lemma: an exact signal that is costly to evaluate and does not lower the exponent

- **Identity.** $y$ is odd and nonzero on the odd subgroup. Gauss's lemma, applied to $j\mapsto kj$ on a half system, gives for $k\ne0$:

  $$\left(\frac kq\right)=\prod_{j=1}^{(q-1)/2}\frac{y(jQ)}{y(jG)}.$$

  This is an exact multiplicative character of the DL with amplitude 1.
- **Hand check** on H027's curve $y^2=x^3+3/\mathbb F_7$, $q=13$, $G=(1,2)$. The $y$-values of $1G..6G$ are $2,3,2,5,3,3$, with product $\equiv1$.
  - $k=2$: the product is $3\cdot5\cdot3\cdot4\cdot5\cdot5\equiv-1=(2/13)$. ✓
  - $k=3$: the product is $\equiv1=(3/13)$. ✓
- **Evaluation cost.** The ordered half-orbit product reduces to an "EDS factorial", $\prod_{i\le N}W_Q(i)$. Its nodal degeneration is a q-Pochhammer product. From memory, baby-step/giant-step polynomial evaluation (Bostan–Gaudry–Schost, √élu) gives about $\tilde O(\sqrt q)$. I know no polylog method; the problem is analogous to the factorial-mod-p and half-factorial-sign problems.
- **Recovery is the decisive falsifier.** Even a free oracle for $\chi_q(ck+d)$ is exactly Legendre-PRF key recovery with chosen queries. H042 recorded root's read of KKK: square-root time with fourth-root queries. I only saw search snippets of BBUV and did not read it. So the exponent does not change unless the Legendre PRF also falls. With an $\tilde O(\sqrt q)$ oracle the total is worse than baseline.
- **Higher residue symbols.** They need μ_m-eigenfunctions built from $[u^i]$, which costs $O(q)$ per product. Rejected.

## D. Cross-modulus beat and integer-representative leakage: closed

- **Coordinate reduced mod q.** Features like $e_q(t\,\tilde x(P))$ that reduce coordinate integers mod $q$ have $\mathbb F_p$-Fourier L1 of $O(\log p)$, including the carry term after differencing. H041's bound then gives $O(\log p)\,q^{-1/4}$.
- **The integer representative in exact identities.** The integer representative $\tilde k$ does appear exactly, in $b(kG)=\tilde k\,b(G)-\sum_{j<\tilde k}\lambda(jG,G)$. But it is tied to an incomplete orbit sum, and the same barrier appears in C. The archive's lift/carry records already cover this.

## E. Failed idea: rational (1,q) quotient

- The integer-matrix automorphism $(P_1,P_2)\mapsto(P_1,P_2-\tilde kP_1)$ identifies $E^2/\langle(G,Q)\rangle$ with $E/\langle G\rangle\times E$.
- My unverified computation says the descended polarization class involves $1+\tilde k^2$ and $\tilde k$.
- Building it publicly needs a degree-$q$ isogeny (√élu scale at best, from memory), and decoding the class is unpriced. It does not get below $\sqrt q$, and it is close to H027's raw note.

## Structural takeaway for root (my inference, not an impossibility theorem)

- $\gcd(q,p(p-1))=1$ forces every homomorphic or bilinear part of an $\mathbb F_p$- or $\mathbb F_p^*$-valued elliptic cocycle on $\mathbb Z/q$ to be trivial.
- The canonical cheap objects (Miller/ζ, EDS/σ, pairings with $q\nmid p-1$) are cocycles of depth at most 2. Their chirp correlations are bounded by Weil-type estimates.
- Genuine mod-$q$ structure (the integer representative, sign patterns) appears only through ordered incomplete orbit sums or products.
- **Missing primitive:** polylog evaluation of an ordered incomplete orbit product. Even that would only give the Legendre bit.
- **Uncovered and not signals:** arbitrary non-character functions such as bits of $b$ or $\varphi$, and objects of depth 4 or more.

## Sources

- I did not re-read Kohel–Shparlinski, Chen or Shparlinski–Stange. I used their bounds as recorded in the accepted root reads (H003, H040, H041).
- The ψ-identity and the Legendre-PRF attack costs beyond H042's KKK record are from memory.

## Mandatory wave report

- **Best supported estimate:** exponent 1/2, generic square-root baseline.
- **Verified improvement:** NONE.
- **Hypothesis under test:** whether a cheap public elliptic-recurrence observable has a large chirp coefficient. For the canonical classes, bounded-L1 post-processing cannot reach $\gamma<1/22$.
- **Evidence:**
  - Paper bounds: A at $2Lq^{-1/4}$, B at $\sqrt2Lq^{-1/8}$, D at $O(\log p)\,q^{-1/4}$.
  - C: the exact Gauss-lemma signal passed the hand check, and its recovery reduces to Legendre-PRF key recovery at about $\sqrt q$.
  - Inconclusive: non-character functions of $b$ and $\varphi$.
- **Next useful analysis:**
  - Have a reviewer check the addition-law derivation and the two-step bound in B.
  - Separately, ask whether any polylog algorithm exists for the EDS factorial or the q-Pochhammer half-product. Its degenerate form is a self-contained question about $\mathbb F_p^*$ subgroups.
  - I recommend no experiment.

---
*Factory usage — local bridge. This turn: 1,954,007 tokens · ≈1,287,372 Factory credits. Saved session total: 1,954,007 tokens · ≈1,287,372 Factory credits (including recorded subagents). Credits are a local estimate, not a dollar charge.*
