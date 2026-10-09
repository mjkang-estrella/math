# H047 Factory Opus shared-information report — UNACCEPTED

2026-10-09 UTC. Provider acpRegistry_factory_droid / claude-opus-5-5.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h047-shared-information-factory-opus-20261009-r1`.
Terminal completed, no pending child runs. task_status again exposed only
'Plan is up-to-date' plus a usage footer. Actual untruncated research output
recovered with t3_thread_read at position35, item
`turn-item:provider:acpRegistry:native-item:provider-instance%3AacpRegistry_factory_droid%3Af029d58e-b56b-4137-925e-f93adaf26ed9%3Aturn%3A1%3Aassistant%3A0`.
This raw report is not an accepted gain or negative theorem. Root identified
an order-four eigenvalue-sign inconsistency, upper-invoice versus lower-bound
leaps, and unsupported general decoder/evaluator closure. Separate native
mathematical and cost/prior-art reviews are required. The stopped H038 route
is not reopened. One primary abstract-only read is disclosed below; no claim
of a fresh full-text audit. No new experiment or Lean claim.

I have one mechanism with complete costs, one new exact identity whose evaluator is blocked, and a recommended decision. Neither card predicts a gain. On paper, both lose to the accepted baseline, which stays at exponent 1/2 with verified improvement NONE. I didn't find a third mechanism that wasn't a duplicate or padding.

Conduct: read-only. I read RESEARCH_LOOP.md, RESEARCH_TEAM.md, the top of STATE.md, the three assigned files, and the archive records listed under "Rejected" below. I opened no H047 file, ran no experiments, launched no children and wrote nothing. The one fresh primary check reached only the abstract and index entry of Duursma–Gaudry–Morain (Asiacrypt 1999, HAL inria-00511639), not the full text. Everything else is either an archive pointer or labelled as from memory.

## Card 1: Borrowed automorphisms on an eigenline of $E^2$ (computed loss)

- **Public operation.** Any curve gets cheap finite-order automorphisms on $E^2$ from integer matrices. Take $\sigma(P_1,P_2)=(-P_2,P_1)$ (order 4, needs $q\equiv1 \bmod 4$) or $\sigma(P_1,P_2)=(P_1-P_2,P_1)$ (order 6, needs $q\equiv1 \bmod 3$).
  - Let $\zeta\in\mathbb F_q$ be the matching eigenvalue: $\zeta^2=-1$ for order 4, $\zeta^2-\zeta+1=0$ for order 6.
  - The line $L=\{(nG,\,n\mu G)\}$, with $\mu=-\zeta^{-1}$ (order 4) or $\mu=\zeta^{-1}$ (order 6), is a cyclic group of order $q$. On $L$, $\sigma$ acts as multiplication by $\zeta$.
  - Set $G_L=(G,\mu G)$ and $V=(Q,\mu Q)=kG_L$. This costs two paid scalar multiplications.
- **Scalar recovery.** Run standard distinguished-point rho on the classes $L/\langle\sigma\rangle$, then verify $kG=Q$.
- **Predicted cost.** About $\sqrt{\pi q/(2r)}$ steps, each needing at least $g=2$ curve additions. Compared with negation-rho, $\sqrt{\pi q/4}$ additions, the ratio is at least $g\sqrt{2/r}$:
  - Order 4: canonicalization is free (compare $x(P_1)$, $x(P_2)$ and signs), so the loss is $\sqrt2\approx1.41\times$.
  - Order 6: picking a canonical representative needs $x(P_1-P_2)$, which costs a third addition, so the loss is about $1.73\times$. Even if that were free, the loss would be $1.155\times$.
  - $E^g$ in general: a gain needs $r>2g^2$, but $\varphi(r)\le g$ forces $r=O(g\log\log g)$. So it always loses.
- **Other costs.** Memory, distinguished-point storage and success probability are as in standard rho. The extra fruitless cycles from the larger class group only make it worse.
- **Prior art.** Duursma–Gaudry–Morain (automorphism class speedup; abstract only). Bernstein–Lange–Schwabe negation is an archive pointer. Viewing $E^2$ as Serre's tensor construction $E\otimes\mathbb Z[i]$ is from memory.
- **Main unsupported assumption.** That an eigenline point can be updated for less than about $1.4$–$1.7$ curve additions. The only way to derive one coordinate from the other is the scalar map $[\mu]$, which costs $O(\log q)$.
- **Cheapest falsifier.** Count field operations per eigenline step against one affine addition (from the Explicit-Formulas Database). This is already decided on paper: rejected.
- **Side observation.** A hyperbolic matrix such as $[[1,1],[1,0]]$ acts on its eigenline as multiplication by a large-order $\lambda$ for one curve addition. That is a cheap multiplier, which H014's short-generator backend lacks. It still needs H014's unsupplied coset label, and it gives no class reduction.

## Card 2: Eisenstein transfer on $E^2$ gives quartic, cubic and sextic residue symbols of $k$ (identity only)

- **Identity.** Take $\varphi(P_1,P_2)=y(P_1)+\iota\,y(P_2)$ with $\iota^2=-1$ in $\mathbb F_p$ or $\mathbb F_{p^2}$. Then $\varphi\circ\sigma=\iota\varphi$, and $\varphi$ has low degree. The order-6 case uses an analogous weighted sum that includes $y(P_1-P_2)$.
  - Let $S$ be any set of representatives of $\mathbb F_q^*/\mu_r$. Write $ks=\zeta^{e(s)}\pi(s)$, where $\pi$ permutes $S$. Then
    $\prod_{s\in S}\varphi(sV)\,/\prod_{s\in S}\varphi(sG_L)=\omega^{E}$, where $\zeta^{E}=k^{(q-1)/r}$.
  - The proof is the Gauss-lemma argument with $\pm1$ replaced by $\mu_r$. One public check that the reference product is nonzero rules out zero factors.
  - This shows that higher scalar residue symbols need an equivariant function, not complex multiplication on $E$; $E^2$ supplies one for every curve.
- **Where it blocks.** Product-tree evaluation needs $S$ to be a union of a few intervals. The only such $\mu_4$ systems I can see come from the two-squares (Gaussian-integer) fundamental domain. That is height-lattice geometry inside the closed H038 stop, so I did not pursue it.
  - The elementary route costs $O(q)$.
  - Even if a block-structured $S$ existed, the block function lives on $E^2$, so its dense representation has about $m^2$ coefficients. That gives about $q^{2/3+o(1)}$ with fast multivariate multipoint evaluation (from memory).
- **Recovery.** At most $\log_2 12$ bits, which leads back to power-residue PRF key recovery. There is no gain.
- **Cheapest falsifier.** A root paper check of the equivariance and the transfer step. Retain only as negative evidence.

## Rejected or duplicate (one line each)

- **Sharing work across shifted targets in product trees.** Each $\chi(k+d)$ needs a tree with step $Q+dG$. Within those trees, the points $\{(j,jd)\}$ that $M$ shifted half-orbits use fall into long common progressions only along the separate per-shift columns. This limit applies to that representation, not to all circuits. It extends the H046 displacement note.
- **Line-function zero test over the half-orbit.** This gives an exact "most significant bit of $k^{-1}$" oracle, and $\log q$ queries recover $k$. Each query, though, is an interval-membership test that costs as much as baby-step giant-step. Duplicate of H036 Card 2 and H040.
- **Signed sums $\sum_{j\in H} g(jQ)$ and the polynomial $\prod_j(Z-y(jQ))$.** Computable in soft-$\sqrt q$ and they determine $k$, but they behave like unstructured hashes. Inverting them is a collision search on an expensive hash, which costs at least $q$.
- **Coset fingerprints over a subgroup $K$.** At least $h=|K|$ work per evaluation, plus a birthday search over $(q-1)/h$ cosets, gives $\sqrt{qh}\ge\sqrt q$. Overlaps H013 and H014.
- **An elliptic analogue of Mordell's half-factorial sign theorem.** Even a polylog formula for the half-orbit product $A(P)$ would only be a free Legendre oracle.
- **Additive Fourier transforms over the shift.** These need all $q$ values, and the Legendre spectrum is flat with coefficient size $q^{-1/2}$.

## Strongest next decision

Close the half-orbit evaluator-sharing sub-question as unable to change the conclusion, and admit no experiment.

- Even free polylog $\chi(k+d)$ queries still meet the BBUV and KKK decoding envelope of about $\sqrt q$. That is archived in H027 and H045, as known upper bounds rather than lower bounds.
- At soft-$\sqrt q$ per bit, the literal route needs about $q^{1/4}$ bits, which costs at least $q^{3/4}$.
- So neither sharing nor a faster single-bit evaluator changes the exponent on its own. This route should reopen only if someone supplies a chosen-query Legendre or power-residue key recovery in $o(\sqrt q)$. That is a separate, well-known open problem, not an ECDLP test.
- Optional cheap step: a paper review of Card 1's arithmetic and Card 2's transfer identity, to file them as negative evidence.
