# H046 raw Factory Opus public-operator report — UNACCEPTED

2026-10-09 UTC. Provider acpRegistry_factory_droid / claude-opus-5-5.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h046-primary-public-operators-factory-opus-20261009-r1`.
Task terminal completed, no pending children. task_status summary contained
only 'Plan is up-to-date' and a provider usage footer. Root recovered the actual
completed assistant research report from the backing thread at position52,
item `turn-item:provider:acpRegistry:native-item:provider-instance%3AacpRegistry_factory_droid%3A337b9971-a74d-4e19-ab48-8088193ab300%3Aturn%3A1%3Aassistant%3A0`, using t3_thread_read.
No new primary sources were read by this proposer; archive pointers are stated
as such below. Mathematical/cost claims await independent review. No test admitted.

I found no construction in this lens that clears the complete-work gate. The working exponent stays 1/2 and the verified gain is NONE. I built four distinct mechanisms. Cards A–C each end in a scoped paper kill that I did not find in the archive. Card D lowers the bar for an existing open primitive but does not supply that primitive. I did not manufacture a surviving card.

## Card A: low-degree polynomial filter on progression lists (scoped kill)

- **Operation.** This uses the four-list/representation structure from H021 with progression lists, scalar $s=a+bn$, and $L=n^2$. The filter is $\hat W=\{P: F(x(P))=0\}$, where $\deg F=D$ and the roots are rational abscissae, so the density is $\delta\approx 2D/q$.
- **Detection.** Form $E_J(X)=\prod_{j\in J}\mathrm{Res}_W(F(W),S_3(X,x(jH),W))$. Each $S_3$ coefficient has degree at most 2 in $X$, so the product has degree $2D|J|$. Multipoint-evaluate it at the $|I|$ giant-step abscissae, using the square-root Vélu (BDLS) structure.
- **Extraction and recovery.** Scan the $|J|$ candidates in each block that evaluates to zero. Then do an exact signed hash match, recover $k$ from the labels and verify.
- **Cost.** $\tilde O(D|J|+|I|+\delta L|J|)$ with $|I||J|=L$. Four-list success needs $L^2\delta\gtrsim q$, so $D\gtrsim q^2/(2L^2)$. For any block shape, $D|J|+L/|J|\ge 2\sqrt{DL}\gtrsim\sqrt2\,q/\sqrt L\ge\sqrt{2q}$ for all $L\le q$. Equality only occurs at $L\approx q$, $D\approx1$, which is ordinary BSGS.
- **Prior art.** BDLS was read by root (recorded in the H019 and H004 records). H020 card 2(a) covered only the interval filter, and H013 covered box products. This kill extends to every polynomial filter of degree $D$ in this detector family. It is not a lower bound for other detectors.
- **What would reopen it.** A detector that never forms the degree-$2D|J|$ product, which means a compact high-degree filter (see Card D).

## Card B: borrowing the Delaplace–May subfield filter through a non-rational isogeny (scoped kill)

- **Construction.** Take a small odd prime $\ell\mid t$, the trace. Then $\pi^2$ acts on $E[\ell]$ as the scalar $-p$. Any line $K$ that is not a $\pi$-eigenline is stable over $\mathbb F_{p^2}$ but not over $\mathbb F_p$. So $E'=E/K$ is defined over $\mathbb F_{p^2}$, generically with $j(E')\notin\mathbb F_p$, and the isogeny $\varphi$ preserves $k$. On $E'$, the condition "$x\in\mathbb F_p$" is linear in Weil-restricted coordinates.
- **Why $\ell\mid t$ is needed.** If $\pi^2=1$ on $E[\ell]$, then $\pi=-1$, because eigenvalue 1 is impossible when $\#E(\mathbb F_p)=q$ is prime. Every quotient is then $\mathbb F_p$-rational, and no subfield filter appears.
- **Kill by counting.** $E'(\mathbb F_{p^2})$ has about $p^2$ points and about $2p$ subfield-abscissa points. The expected number inside $\varphi(\langle G\rangle)$ is about 2. A character-sum bound on the genus-2 curve $w^2=N(f'(x))$ would allow at most $O(\sqrt p)$; this is my inference and I have not proved it.
  - With about 2 points, the filter density is about $1/q$, which is useless.
  - Even with $O(\sqrt p)$ points ($\gamma=1/2$), the lists must have size $n=q^{3/8}$. Delaplace–May's recorded zero-join exponent (from H004) then costs about $q^{0.656}$.
  - Working in the whole group instead brings back their own baseline of $p$.
- **Prior art.** H004 card 3 stopped at "there is no subfield over $\mathbb F_p$". It did not consider an isogeny transfer.

## Card C: halving recursion for interval kernels (scoped kill)

- **Mechanism.** Use a Gauss-multiplication (halving) identity for $I_L(X)=\prod_{j\le L}(X-x(jG))$. The rational zeros of $I_L\circ[2]$ are $\pm[1,L/2]G\cup\pm(H'+[0,L/2)G)$, with $H'=\frac{q+1}{2}G$.
- **Extra factor.** There is also a factor $J$ that is a norm from $\mathbb F_{p^3}$. It is an interval product of length $L$ translated by 2-torsion points (for an odd-order curve, $f$ is irreducible).
- **Cost.** Unrolling to depth $t$ needs $I_{L/2^t}$ at $2^t$ points. At BDLS cost that is $\tilde O(\sqrt{2^tL})\ge\sqrt L$, and $J$ adds another product of the same length. No depth saves anything.
- **Prior art.** This parallels the factorial-mod-$p$ situation, where Bostan–Gaudry–Schost (root read it for H046) is still the square-root method. It is distinct from H036's holonomic route and from H045's EDS-factorial analogy.

## Card D: low-density regime of the four-list compact-filter route (gate refinement; primitive still missing)

- **Mechanism.** H021's four-list route with a $\mu_u$ filter of density $q^{-\gamma}$, where $u=(p-1)/d$ and $d\approx q^\gamma$ (this requires $d\mid p-1$).
- **Parameters.** H021's second-moment condition gives list size $n=q^{(1+\gamma)/4}$ and level-1 output $q^{(1-\gamma)/2}$.
- **Requirement.** If the join costs $n^{2-\theta}$, the total is $q^{\max((1+\gamma)(2-\theta)/4,\,(1-\gamma)/2)}$. This beats $\sqrt q$ if and only if $\theta>2\gamma/(1+\gamma)$. For example, $\gamma=0.1$ needs a join below $n^{1.818}$, with a best possible total of $q^{0.45}$.
- **What this changes.** H021 asked for an index that is output-sensitive up to polylog factors. The refinement only asks for a polynomial saving over the naive join, which means skipping all but about a $d^{-1/2}$ fraction of pairs.
- **Why it is still open.** Per-pair Lucas or resultant reporters (H043) have $\theta=0$ by construction, and block aggregates pass through an $n\beta$-dimensional quotient algebra (H044, Astra). I supply no operator that skips pairs.

## Strongest potential test

This is a paper question for an independent reviewer on Card D.

Either exhibit a join for two length-$n$ progressions with a $\mu_u$ filter that never evaluates more than a $d^{-1/2}$ fraction of pairs, or prove a scoped lemma: any block aggregate built from $\prod_{b\in\text{block}}(Z-x(A+bH))$ needs $\Omega(\beta)$ work per query and block.

A low-rank sub-route is already blocked at full period by H017 Fact A (linear complexity is at least the embedding degree). Even a low rank on short windows would only turn the join into an incidence-search problem; it would not by itself give a subquadratic join. No experiment is needed to decide this.

## Considered and not carded (known walls)

- **Kani–Robert isogeny interpolation (H004).** It needs torsion images the ECDLP input does not provide.
- **Global torsion lifts (H015).** Already examined, with the missing construction recorded there.
- **Trace from $E(\mathbb F_{p^n})$.** Each relation succeeds with probability about $(B/p)^n$, which loses.
- **Genus-$g$ covers of $E$.** Jacobian index calculus costs about $p^{2-2/g}$, far above $\sqrt q$; this figure is from memory and I did not reread a source.
- **Rho on large endomorphism orbits.** Canonicalizing an orbit is equivalent to computing $[k^m]G$ from $kG$, which is a power Diffie–Hellman problem.

## Process

- Everything was read-only: no scripts, experiments, files, child tasks or commits.
- I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, the top of STATE.md, and the H004, H010, H011, H015, H019, H020, H021, H024, H041, H043, H044 and H045 records.
- I opened `H046-half-orbit-evaluator.md` after a search surfaced it. It is a root finding, not a proposal, and it already covers a square-root evaluator I had derived independently, so I dropped mine. I did not read the H046 briefs or any other agent's proposal.
- I read no new primary sources this session. All prior-art pointers come from primary reads recorded in the archive, and the claims above are my own paper derivations.
