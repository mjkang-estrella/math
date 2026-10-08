# Unaccepted H002 lifting reviewer report

Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h002-lift-math-review-20261008-r1`.
Provider/model: `acpRegistry_factory_droid/claude-fable-5.1`; status completed.

Retained evidence; conclusions require scope/algorithm review before adoption.
No experiment is automatically authorized by the report.

## A2 review: compressed accumulated defect of a p-adic section

Scope: read-only analysis of A2 in `research/hypotheses/H002-astra-arithmetic-cards.md`. No experiments run. Sources checked today: Smart, *J. Cryptology* 12 (1999) 193–196, DOI 10.1007/s001459900052 (abstract page); Filippone, arXiv:2304.14150v1, full HTML text including Theorem 5.1 and Section 6. W019 findings consulted only for the known ring-arithmetic failure mode.

### 1. Definition check: $g$ is well defined, under stated conditions

Setting: $E/\mathbb{F}_p$ ordinary, $\#E = n$ prime, $n \ne p$, $p \ge 5$. Fix any Weierstrass lift $\tilde E/(\mathbb{Z}/p^2)$. Reduction gives $0 \to E_1 \to \tilde E(\mathbb{Z}/p^2) \to E(\mathbb{F}_p) \to 0$ with $E_1 \cong p\mathbb{Z}/p^2 \cong \mathbb{F}_p$ via $t = -x/y$ (formal log is $t - \tfrac{2a}{5}t^5 - \dots$, so $\log \equiv t \pmod{p^2}$ on $E_1$).

- $[n]s(R)$ reduces to $[n]R = O$, so it lies in $E_1$ and $\log([n]s(R)) \in p\mathbb{Z}/p^2$. Dividing by $p$ is exact.
- $n$ is a unit mod $p$: Hasse gives $n \in (p+1-2\sqrt p,\ p+1+2\sqrt p)$ and the only multiple of $p$ there is $p$ itself (excluded). So $g(R) = \log([n]s(R))/(np) \in \mathbb{F}_p$ is well defined.

Structural meaning (this is the key fact the card does not state): because $\gcd(n,p)=1$ the extension splits uniquely, $\tilde E(\mathbb{Z}/p^2) = T \oplus E_1$ with $T = \tilde E(\mathbb{Z}/p^2)[n]$ the unique homomorphic section $\tau$. Write $s(R) = \tau(R) + \delta(R)$, $\delta(R) \in E_1$. Then $[n]s(R) = [n]\delta(R)$ and

$$g(R) = t(\delta(R))/p =: d(R).$$

So $g$ is exactly the $E_1$-coordinate of the offset of $s$ from $\tau$. Geometrically, measuring the fiber displacement with $\omega = dx/2y$: $d(R) = \pm\big((\hat x_s(R) - x(\tau(R)))/p\big)/(2y_R) \bmod p$, i.e. the second $p$-adic digit of the $x$-coordinate of the canonical torsion lift relative to the chosen $x$-lift, over $2y$. Note $\tau$ itself is computable in $O(\log n)$ ring operations ($\tau(R) = s(R) - \delta(R)$, with $\delta$ rebuilt from $t$ by scaling by $n^{-1}$ in $\mathbb{F}_p$), so nothing is hidden in $\tau$.

### 2. The accumulated-defect identity is a tautology, and that reshapes the hypothesis

$c(R,S) = d(R)+d(S)-d(R+S)$ is the coboundary $\partial d$. Summing $c$ along any addition chain for $k$ telescopes, so

$$C_k = k\,d(P) - d([k]P),$$

independent of the chain. The identity $g([k]P) = k\,g(P) - C_k$ is therefore exact but content-free: the solver knows $d(P)$ and $d(Q)$ (each $O(\log n)$) and the unknown $C_k$ is just $k\,d(P) - d(Q)$, a rewrite of $k$. The card's remark that a small local alphabet does not imply a small complete set is correct, but the stronger statement is that the chain plays no role at all.

Consequently, with $\lambda := d(P) \neq 0$ and $\hat\ell(R) \in [0,n)$ the integer discrete log, A2's hypothesis is *equivalent* to:

$$d(R) \equiv \lambda\,\hat\ell(R) - c(R) \pmod p,\qquad c(R) \in C,\ |C| = n^{\alpha},$$

for the good fraction $\beta$ of $R$. That is, the specific $O(\log n)$-computable function $d$ is a DLP-mod-$p$ approximator up to $|C|$ offsets. A2 supplies no reduction or mechanism; it is the conjecture that this particular function (second digit of the torsion lift's $x$, over $2y$) tracks $\hat\ell$. Two structural notes:

- $\hat\ell \bmod p$ is not a function on the group $\mathbb{Z}/n$ (it depends on the choice of representatives in $[0,n)$, with $\partial\hat\ell \in \{0, n\}$). So small $|C|$ requires $d$ to be close to a *non-group-theoretic* object. Any exact group-theoretic symmetry of $d$ is evidence against, and Section 4 exploits this.
- Approximately additive functions with two-valued coboundary do exist ($\hat\ell$ itself), so I am not rejecting the nonhomomorphic idea for the reason the card already discounts. The burden is only cheapness.

### 3. Section family: what "bounded rational corrections" actually span

Every section has the form $\hat x = \hat x_0 + p\,\varphi(R)$, $\hat y$ the Hensel lift ($2y$ unit). By the fiber-displacement formula, exactly

$$d_\varphi(R) = d_0(R) + \varphi(R)/(2y_R).$$

Curve-lift changes: lifts of $E$ to $\mathbb{Z}/p^2$ up to isomorphism form a one-parameter family ($j$-digit $w$). Isomorphic lifts ($u \equiv 1 \bmod p$) only reparametrize $\varphi \mapsto \varphi + 2wx$. Changing $w$ changes $T$ and gives $d_{0,w} = d_{0,0} + w\,H(R)$ with $H \propto -(\partial_w \psi_n)(x)/(\psi_n'(x)\,2y)$: computable in $O(\log n)$ but of degree $\Theta(n^2)$, not a low-degree feature. For $j \in \{0,1728\}$ all lifts are isomorphic (consistent with W019's observation for $y^2 = x^3 + b$), so $w$ is absent there.

So the full cheap family is $d = d_0 + wH + \varphi/(2y)$ with $\varphi$ in a bounded-degree rational space. The hypothesis then says $\lambda\hat\ell \in d_0 + wH + \mathrm{span}(F)/(2y) + C$. A counting heuristic ($\le p^{m+1}$ family members versus $\binom{p}{|C|}|C|^n$ small-image functions) is unfavorable but not rigorous, since $d_0$ is not random. The "few affine features" test the card proposes checks the right object but cannot by itself be decisive.

### 4. Symbolic obstruction (the cheapest decisive analytic test I found)

**Negation.** If $\varphi$ depends on $R$ only through $x$, then $s(-R) = -s(R)$, $\tau(-R) = -\tau(R)$, so $d(-R) = -d(R)$. With $\hat\ell(-R) = n - \hat\ell(R)$ this forces only $C = \lambda n - C$: a symmetry, no contradiction.

**Extra automorphisms, equivariant sections (rigorous).** Take $j = 0$, $p \equiv 1 \bmod 3$ (the secp256k1 shape), lift $y^2 = x^3 + \hat b$ with automorphism $\tilde\zeta(x,y) = (\hat\zeta x, y)$, $\hat\zeta$ the Teichmüller cube root of unity. Use the Teichmüller $x$-lift $\hat x = \omega(x)$ (equivalently $x_0^p \bmod p^2$) and $\varphi$ in the $\zeta$-eigenspace ($\varphi(\zeta x, y) = \zeta\varphi(x,y)$). Then $s(\zeta R) = \tilde\zeta s(R)$ exactly, $\tilde\zeta$ preserves $T$ so $\tau(\zeta R) = \tilde\zeta\tau(R)$, and $\tilde\zeta$ acts on $E_1$ by $t \mapsto \zeta t$. Hence $d(\zeta R) = \zeta\, d(R)$ **exactly**. (For $j = 1728$ the same holds with $(x,y) \mapsto (-x, \hat\imath y)$ and multiplier $\imath^{-1}$ on $E_1$.)

Let $\lambda_\zeta \in [1,n)$ be the integer with $\zeta R = [\lambda_\zeta]R$. Substituting the hypothesis into $d(\zeta R) = \zeta d(R)$ gives, for every good $R$,

$$c(\zeta R) - \zeta\, c(R) \;\equiv\; \lambda\big[(\lambda_\zeta\hat\ell(R) \bmod n) - \zeta\,\hat\ell(R)\big] =: f(\hat\ell(R)) \pmod p.$$

The left side takes at most $|C|^2$ values. The right side, as $m = \hat\ell$ runs over $[0,n)$, is $\lambda(m' - \zeta m)$ on the lattice points $(m, m') \in L = \{m' \equiv \lambda_\zeta m \ (\mathrm{mod}\ n)\} \cap [0,n)^2$. A fiber $f^{-1}(v)$ is the set of points of a coset of the index-$p$ sublattice $L' = \{(m,m') \in L : m' \equiv \zeta m \ (\mathrm{mod}\ p)\}$ (equivalently $m' \equiv \mu m \bmod np$, $\mu$ by CRT) inside the box, so $|f^{-1}(v)| \le c\,(1 + n/\lambda_1(L'))$ and

$$|C|^2 \;\ge\; |\mathrm{image}\, f| \;\gtrsim\; \beta'\min(n, \lambda_1(L'))/c .$$

$\det L' = np \approx n^2$, so generically $\lambda_1(L') \approx n$ and $|C| \gtrsim \sqrt{\beta' n}$: **$\alpha \ge 1/2$, no sub-square-root gain**, for every curve lift and every eigen-$\varphi$. The per-curve check is one 2D Gauss reduction of the lattice $\langle(1,\mu),(0,np)\rangle$, $O(\log p)$ integer operations, no curve arithmetic. If a specific curve has unusually small $\lambda_1(L')$, the bound weakens to $|C| \gtrsim \sqrt{\lambda_1}$ and that curve would need a separate look.

**Scope of the obstruction.** It covers only equivariant sections on curves with $\mathrm{Aut} \ne \{\pm1\}$. For the canonical-representative section ($\hat x = x_0$) or non-eigen $\varphi$, $d(\zeta R) - \zeta d(R) = \kappa(R)$ with $\kappa(R) = \big[(\hat\zeta x_0 - \widehat{\zeta x})/p + \varphi(\zeta R) - \zeta\varphi(R)\big]/(2y)$, an explicit Fermat-quotient-type carry plus a bounded-degree rational function. The constraint becomes $f(\hat\ell(R)) + \kappa(R) \in C - \zeta C$: survival requires the cheap function $\kappa$ to cancel a DLP-derived pseudo-random term to within $|C|^2$ values, which is the original conjecture in a new guise, not an escape. For generic $j$ only negation is available and I found no rigorous obstruction; A2 there reduces to the bare conjecture of Section 2.

### 5. Prior art applicability

- **Smart (1999, verified DOI/abstract):** linear-time DLP on trace-one curves. The mechanism is that when $p \mid \#E(\mathbb{F}_p)$ the extension does not split and $[p]$ factors through a lift-independent homomorphism $E(\mathbb{F}_p) \to E_1$. For $n$ coprime to $p$ the extension splits uniquely (Filippone's Theorem 2.1 states this too) and $[n]$ kills $T$, so $[n]s(R)$ sees only $\delta(R)$. Nothing of Smart's mechanism transfers; the card is right. Satoh–Araki's "Fermat quotient" viewpoint is the closest relative of the carry term in $d_0$, but there it is organized into a homomorphism and here it is not.
- **Filippone (arXiv:2304.14150v1, full text verified):** Theorem 5.1 assumes $P, Q \in \mathcal W(\mathbb{Q})$ with $Q = hP$ **over $\mathbb{Q}$**, and even then requires $\bar h = h \bmod t$ from the finite group first (Remark 5.1: "if the cardinality is small, easily determined"), i.e. it presupposes the $\mathbb{F}_p$ DLP. Section 6 also starts from a global relation. For an $\mathbb{F}_p$ instance this is the lifting problem (Silverman, SAC 2009, cited by Filippone as ref. 15), with the known negative history. The card's one-line summary is accurate; no bridge is supplied.
- **Novelty of compressed nonzero defects:** no direct prior art found in the sources checked. Given Section 2, it is a reformulation of "cheap DLP-mod-$p$ approximator" rather than a new mechanism; I would not label it novel.

### 6. Arithmetic prerequisites over $\mathbb{Z}/p^2$ (if anything is ever computed)

- Projective/Jacobian coordinates only; never divide by $x_2 - x_1$ or $2y$ affinely.
- In double-and-add for $[n]s(R)$ with addend $s(R)$: partial sums $[m]s(R)$ reduce to $[m]R \ne O$ for $0<m<n$, so only the final step adds two points congruent mod $p$ to $\pm$ each other ($H = U_2 - U_1 \equiv 0$, $R' = S_2 - S_1 \equiv -2y\cdot$unit). Jacobian formulas then give $Z_3 \in p\mathbb{Z}/p^2$, $X_3 \equiv R'^2$, $Y_3 \equiv -R'^3$ units, and $t = -X_3Z_3/Y_3$ is a valid $E_1$ chart. Branch rule: $H \equiv 0 \bmod p^2$ and $R' \equiv 0 \bmod p^2$: double; $H \equiv 0 \bmod p^2$, $R'$ unit: result is exactly $O$ (then $\hat y_2 = -\hat y_1$ exactly and $d(R)=0$); otherwise generic add even when $H \equiv 0 \bmod p$. Other chains (NAF, windows) need the same mod-$p$ coincidence check before every add.
- Never add two $E_1$ points with curve formulas (the W019 failure mode: a mod-$p^2$ equality test routes distinct kernel points to doubling). Add their $t$-values in $\mathbb{F}_p$; this is exact because $F(t_1,t_2) = t_1 + t_2 + O(t_1t_2)$ and $t_1t_2 \equiv 0 \bmod p^2$.
- $c(R,S)$ needs $s(R+S)$ from the *reduced* sum, not $s(R)+s(S)$.
- Requires $p \ge 5$, $n$ odd (so $y_R \ne 0$), $d(P) \ne 0$ (fails with probability about $1/p$ per section).

### 7. Recommended tests, cheapest first (none run)

1. **T0, zero compute:** ask the proposer to justify why $d_0$ should track $\hat\ell$ at all, given $C_k = k\,d(P) - d([k]P)$. Absent a reason, A2 is a conjecture, not a mechanism, and should not be funded.
2. **T1, $O(\log p)$ per curve:** for $j \in \{0,1728\}$ ordinary prime-order toy curves, Gauss-reduce $\langle(1,\mu),(0,np)\rangle$; report $\lambda_1$. If $\lambda_1 \approx n$ (generic), the equivariant family is rigorously excluded from $\alpha < 1/2$ on that curve, no point arithmetic needed.
3. **T2, DLP-free necessary condition for generic $j$:** for fixed $S$, $\Delta_S d(R) = d(R+S) - d(R)$ must lie in $\{\lambda\hat\ell(S), \lambda(\hat\ell(S)-n)\} + (C - C)$, at most $2|C|^2$ values, with the sets for different $S$ all translates of one fixed set. Decisive quickly for $\alpha < 1/4$. For $\alpha \in [1/4,1/2)$ use the known-log collision rate $\Pr[d(R) - d(S) \equiv \lambda(\hat\ell(R) - \hat\ell(S))] \ge \beta^2/|C|$ versus baseline $\approx 1/p$; roughly $10\,n^{1/2}$ pairs at $O(\log n)$ ring ops each. Any negative result eliminates that section and curve only.

### 8. Unresolved

- No rigorous obstruction for generic $j$ (automorphism group $\{\pm1\}$); there A2 stands or falls on the raw conjecture about $d_0$.
- Whether the carry term $\kappa$ for canonical-representative sections could correlate with $f\circ\hat\ell$: no reason to expect it, not disproved.
- Shparlinski–Stange-type character-sum bounds concern different statistics (characters of division-polynomial values) and do not directly bound second-digit distributions; equidistribution of $d_0$ is heuristic.
- Finite toy outcomes would not settle asymptotics, and the lattice bound in T1 is curve-specific, not a uniform theorem.

Bottom line: the definition is sound; the accumulated-defect identity is exact but adds nothing; A2 is equivalent to asserting that one specific cheap function approximates the integer-representative discrete log mod $p$ up to $n^{\alpha}$ offsets; equivariance rigorously forces $\alpha \ge 1/2$ for the natural (Teichmüller/eigen) section family on $j \in \{0,1728\}$ curves whenever a trivial 2D lattice check passes; neither Smart nor Filippone supplies a bridge for $n \ne p$. I recommend the coordinator treat A2 as not surviving review unless the proposer answers T0 with a concrete structural reason.
