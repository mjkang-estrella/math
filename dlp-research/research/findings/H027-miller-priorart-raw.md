# H027 Miller trace primary-art report (raw)

Status: RAW independent review, not wholesale accepted. Root flagged the blanket Hasse exclusion q not dividing p−1 as false for small curves and will check the claimed multiplicative map's actual domain. No novelty was claimed in the construction. Complex zeta/universal-extension identifications are memory-based in this report, not verified source claims.

Provider: acpRegistry_factory_droid; model: claude-opus-5-5.
TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h027-miller-trace-priorart-factory-opus-20261008-r1
Completed and read 2026-10-08; no child edits/runs reported beyond primary-source access.

## H027 prior-art and recovery-meaning review

**Verdict:** The quantity is already known. The Native "Miller first-local-coefficient" construction is Rück's 1999 algorithm, applied with $q \ne p$. That is exactly the case where Rück's map stops being a homomorphism. No primary source I read gives a scalar predicate or removes the slope defect when $E(\mathbb F_p)$ has prime order $q \ne p$. Removing the defect into any additive $\mathbb F_p$ target is impossible for a group-theoretic reason, explained below; this is not a degree or extension-size argument. Verified improvement: none. I propose no experiment, because there is no positive recovery premise.

### What I actually read
- **Couveignes–Lercier, "Elliptic periods for finite fields"** (ellbasisrev.pdf): full text. Its subject is bases for doing arithmetic in $\mathbb F_{q^d}$, not discrete logarithms. The relevant parts are §2 (the function $u_{A,B}$ and the slopes $\Gamma$), Lemma 1 (requires $db \ne O$) and Lemma 4 ($\sum_{k} u_{kt,(k+1)t}$ is a constant).
- **Joux–Pierrot, eprint 2019/782**: full text through §3.3, read from the arXiv copy (1907.02689) because eprint.iacr.org served a Cloudflare page. This is **finite-field DLP** in small characteristic. The elliptic curve only serves to represent $\mathbb F_{q^k}$. There is no ECDLP content.
- **Semaev, Math. Comp. 67 (1998)** and **Rück, Math. Comp. 68 (1999)**: full text from AMS.
- **Coombes, JPAA 138 (1999)**: **abstract only.** ScienceDirect and CORE both returned Cloudflare bot challenges, and I did not try to bypass them. I make no claim from that paper beyond what its abstract states.
- Statements marked "memory" below were not re-read here.

### What the quantity is
1. **Rück's construction.** Rück's proof expands $df/f$ in a local parameter at $P_0$. It then defines a group law on $S \times k$ through the 2-cocycle given by the local coefficient of the line function $h$, which he calls "the additive version of the Tate pairing". Repeated doubling gives $(D,0)^{p} = (0,\varphi(D))$. Native's "binary Miller adds line slopes to the first local coefficient" is this same algorithm with $p$ replaced by $q$. Semaev's version is equivalent but evaluates $f'/f$ at a point $R$ instead.
   - Both papers need $\#\langle P\rangle = p$. Rück relies on Serre's isomorphism $\mathrm{Pic}^0[p] \to$ holomorphic differentials. When $q = p$, the defect term $q\lambda$ in $a_{Q+R} = a_Q + a_R - q\lambda$ is zero in characteristic $p$, so the map is a homomorphism.
   - When $q \ne p$, $df/f$ has residues $\pm q \ne 0$, Serre's isomorphism does not apply, and the defect remains.
2. **Zeta-function meaning** (my derivation plus the classical identity, from memory). Over $\mathbb C$, $\zeta(u+v) - \zeta(u) - \zeta(v)$ equals the chord slope when $y = \wp'/2$. Also $z = -x/y = u + O(u^5)$. Together these give
   $$a_Q = -q\,Z(Q),\qquad Z = \zeta - (\text{quasi-period linear part}).$$
   So $a_Q$ is $-q$ times the corrected Weierstrass zeta value at a $q$-torsion point. From memory, this is the weight-1 level-$q$ Eisenstein quantity. Equivalently, it is the $\mathbb G_a$ coordinate of the canonical lift of $Q$ into the universal vector extension (Mazur–Messing, Katz; memory).
   - Over $\mathbb F_p$, the algebraic version is forced. $q$ is invertible, so a symmetric cocycle on $\mathbb Z/q$ with values in $\mathbb F_p$ has exactly one trivialisation, because $\mathrm{Hom}(\mathbb Z/q, \mathbb F_p) = 0$.
   - Averaging the cocycle over the group gives $a_Q = \sum_{S\in E(\mathbb F_p)} \lambda(Q,S)$, using $\lambda(Q,O) = \lambda(Q,-Q) = 0$.
   - This full-group sum appears to be the meaning of Native's "Norm/trace = $-a_Q$" statement. It is the same kind of identity as Couveignes–Lercier Lemma 4: a sum of the slope functions over the whole cyclic group is constant. The signs and the degenerate-point terms belong to Sol's exact-algebra audit.
3. **Coombes is a different derivative.** His logarithmic derivative takes values in **absolute** Kähler differentials $\Omega^1_{k/\mathbb Z}$, not the curve differential $df/f$. By the abstract's own statement, its kernel is $E(F)$, where $F$ is the algebraic closure of $\mathbb F_p(a_4,a_6)$ inside $k$. For finite $k$ this is all of $E(k)$, so the map is identically zero. It has no bearing on H027.

### The slope defect under the actual hypotheses
- **Additive targets.** Any map from $E(\mathbb F_p) \cong \mathbb Z/q$ to an $\mathbb F_p$-vector space, or to any $p$-group (for example $\mathbb Z/p^2$ or Witt vectors), is zero if it is a homomorphism. So no post-processing that is linear over $\mathbb F_p$ can turn $a_Q$ into an additive coordinate. This follows from $q \ne p$ alone.
  - This also explains why every known additive or $p$-adic logarithm attack needs anomalous order. Semaev and Rück require it as read. Smart and Satoh–Araki also require it (memory).
- **Multiplicative targets.** The Joux–Pierrot evaluation map $\Psi$ (§2.2, §3.3) is a homomorphism into $\mathbb F_{p^q}^*/\mathbb F_p^*$. With an elliptic basis of degree $q$, its order is $(p^q-1)/(p-1)$, which is $\equiv 1 \pmod q$ whenever $p \not\equiv 1 \pmod q$ (Fermat). That holds here, because Hasse's bound rules out $q \mid p-1$. So $\Psi$ is **trivial** on $E(\mathbb F_p)$. A target with $q$-torsion needs $\mu_q \subset \mathbb F_{p^k}^*$ with $k = \mathrm{ord}_q(p)$, which is the MOV/Frey–Rück route. The embedding degree $k$ is large for generic prime-order curves (memory).
- **Existence of the elliptic basis, without overclaiming.** Couveignes–Lercier's size condition ($d_q \le 2\sqrt q$, Lemma 8) is only sufficient for *constructing* a suitable curve. For a given curve with $d = q$ and $p \not\equiv 1 \pmod q$, Frobenius acts on $E[q]$ with eigenvalues $1$ and $p$. So $(\varphi-1)b = t$ has no solution with $b \in E[q]$, and Lemma 1's condition $qb \ne O$ holds automatically. The basis exists. It is just not needed, because Miller computes $a_Q$ without touching $\mathbb F_{p^q}$.
- **What remains open.** Writing $Q = kP$, we have $a_{kP} = k\,a_P - q\sum_{i<k}\lambda(iP,P)$. This is a fixed, efficiently computable function of $Q$, defined by a path sum. I found no established result that gives a *nonlinear* predicate from it. I also found none that rules one out. The group-theoretic argument above excludes only additive or linear recovery.

### Implications for H027
- Prior-art status: this is Rück 1999 (Semaev 1998 for elliptic curves) with $q \ne p$, plus the classical zeta and universal-extension interpretation. It should not be claimed as novel.
- A positive premise would have to be a specific nonlinear predicate on $Z_p(Q) = -a_Q/q$ that correlates with $k$, with a stated reason why it should. Neither Native nor the literature supplies one. Until that exists, nothing should be admitted to a test.
- For Sol: the identity $a_Q = \sum_S \lambda(Q,S)$, its signs and the degenerate-point conventions are my unverified derivation. I checked the claimed $df/f$ formula only to leading order at $O$ and at $Q$: residues $q$ and $-q$, constant term $a_Q$.

I made no edits to the workspace and launched no subagents. The downloaded PDFs and extracted text are in `/tmp/h027rev`. A background preview tab I opened on the CORE challenge page is still open; nothing was submitted through it.
