# H026 representation proposals — raw, pending independent reconciliation

TaskId: node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h026-representation-hybrids-grok-20261008-r1

Primary normalization/cancellation, literal support costs, and sign-bias
conversion are not yet accepted. No optional numerical test is admitted.
Claims that a source exponent is erroneous need checking against its exact
normalization. Global bias alone does not guarantee concentration in each
unknown-index window. Earlier EDS scopes remain authoritative meanwhile.

Scoped no-survivor. Three two-view mechanisms price out against negation rho and x-only interleaved baby-step giant-step. None supplies a complete-work gain. Verified improvement stays **NONE**. Nothing was edited, run, or committed. No other H026 proposal was read.

The public inputs are an ordinary curve \(E/\mathbb{F}_p\), a generator \(G\), and \(Q=[k]G\). The group order \(q\) is prime, \(q\neq p\), \(q\approx p\), \(\gcd(q,p-1)=1\), and the only rational automorphisms are \(\pm 1\). Low-memory comparison is the project negation-rho ledger, about \(\sqrt{\pi q/4}\) batched additions at \(5M+1S\). High-memory comparison is the H019 x-only specialization of Galbraith–Wang–Zhang, about \((2\sqrt{2}/3)(2.5+s)\sqrt{q}\) multiplications. Those two constants are project comparators; the Galbraith–Wang–Zhang PDF and Bernstein–Lange–Schwabe 2011/003 were not re-opened in this session. Signed layout B is not retuned.

## 1. \(\varphi\)-mask against the order translate

**Public computation.** Let \(W(n)=\psi_n(G)\) and let \(\varphi\) be the Lauter–Stange normalization. Their displayed net identity is \(W_{[n]G}(\ell)\,W(n)^{\ell^2}=W(n\ell)\). Comparing \(\ell=p-1\) and \(\ell=p-1+q\), then taking the unique \(q^2\)-th root in \(\mathbb{F}_p^\times\) (which exists because \(\gcd(q,p-1)=1\)), gives
\[
\varphi([n]G)=\varphi(G)^{n^2}W(n).
\]
The exponent \(2(p-1)q^{-1}\) is \(0\) in \(\mathbb{Z}/(p-1)\mathbb{Z}\), so it contributes the factor \(1\). The arXiv HTML writes \(n^2-1\); that rearrangement disagrees with this reduction. TCHES 2026, Theorem 2, states \(n^2\). Thus \(W(n)=\varphi([n]G)\,\gamma^{-n^2}\) with \(\gamma=\varphi(G)\).

Both \(\gamma\) and the three values \(\varphi(Q-G),\varphi(Q),\varphi(Q+G)\) are functions of known points. Each is one elliptic-net evaluation at the known indices \(p-1\) and \(p-1+q\), charged at the paper’s \(O((\log p)^3)\) field operations. The order-translate ratio
\[
L=W(q+1)W(2)/W(q+2)
\]
is the same kind of evaluation at known indices. Substitution gives \(L=\gamma^{2q}\) and
\[
W(2)\,W(kq+1)/W(kq+2)=\gamma^{2kq}=L^k.
\]
The masked ratio \(\beta=W(k-1)/W(k)\) is \([\varphi(Q-G)/\varphi(Q)]\,\gamma^{2k-1}\). Fed into the rank-2 transformation (their equation (9), rebuilt here from Theorem 2.2), it produces the same power \(\gamma^{2kq}\).

**Recovery.** There is nothing left to recover. After the mask is substituted, both sides equal \(\gamma^{2kq}\). The coefficient of \(k\) cancels.

**Gain.** None. This is the natural two-view reading of EDS Association: one view from \(Q\) through \(\varphi\), the other from the known order lattice of \(G\). They are the same identity.

**Costs.** Three net evaluations plus the constant \(L\). No list, no restarts. Failure mode is algebraic dependence, not a missed collision.

**Prior art read this session.** Lauter–Stange, arXiv:0803.0728v2, Theorems 2.1–2.4 and 3.1 and the derivation of (9). Liao–Zhang, TCHES 2026(3), 518–540, Sections 2.3–2.4 and Theorem 2, from the publisher PDF. Shipsey–Swart 2008/444 was not used: it needs \(\#E=p-1\).

**Unsupported assumption.** None for the identity. The assumption that would have produced a gain — that the two views are independent enough to leave a nontrivial \(\mathbb{F}_p^\times\) equation \(A^k=B(Q)\) — is false for this pair.

**Falsifier.** The exponent arithmetic above. An independent check only has to confirm \(\varphi([n]G)=\gamma^{n^2}W(n)\) at \(n=2\) on one ordinary curve; a wrong exponent changes the identity, and the corrected one still cancels.

## 2. Doubling genealogy of a \(Q\)-block against a \(G\)-list

**Public computation.** Liao–Zhang build two lists from \(G\) alone: \(\{h_{iM}\}\) and the support \(\{h_{2i}\}\), \(\{h_{i-1}h_{i+1}\}\) for \(i<M=\lceil\sqrt{q}\rceil\), by the doubling recurrences (11)–(12) and (15)–(16). From \(Q\) alone they build the width-3 block \(B_k\) by three applications of (7). Children are then
\begin{align*}
h_{k-2\ell}h_k&=h_{k-\ell+1}h_{k-\ell-1}h_{2\ell}-h_{\ell+1}h_{\ell-1}h_{k-\ell}^2,\\
h_{k-2\ell-1}h_{k+1}&=h_{k-\ell+1}h_{k-\ell-1}h_{2\ell+1}-h_{\ell+2}h_\ell h_{k-\ell}^2,
\end{align*}
their (17)–(18). Every term on the right is either in the \(Q\)-block genealogy or in the \(G\)-support list.

**Recovery.** A match \(\pm h_{iM}=h_{k-j}\) is tested by one scalar multiplication \(Q\stackrel{?}{=}[j\pm iM]G\). The coefficient of \(k\) is \(1\). Their Remark 1 records that \(h\)-collisions are not index equalities; false hits pay that scalar multiplication. At \(q\approx N\) they bound the wasted hits by a small constant, so verification is \(O(\log q)\) field operations per solve, not a leading term.

**Gain that does not survive.** A successive block step is quoted at \(3.5M+0.5S\) with no inversion, and negation cuts the giant range in half. That would matter only if the support were smaller than the x-only baby list. It is not. A binary-doubling tree that emits \(M\) distinct baby indices has \(\Theta(M)\) nodes, and the parent labels \(\ell\) are \(\Theta(M)\) distinct integers. Each parent consumes its own \(h_{2\ell}\). The even indices \(2\ell\) are already \(\Theta(\sqrt{q})\) field elements. H021’s screen puts a fresh auxiliary list of that length, at \((3.5+s)\sqrt{q}\) multiplications, strictly above the x-only interleaved count \((2\sqrt{2}/3)(2.5+s)\sqrt{q}\) (about \(3.11\sqrt{q}\) versus \(4.3\sqrt{q}\) at \(s=0.8\)) before the search loop starts. A proper subtree that emits only \(o(\sqrt{q})\) indices covers \(o(q)\) scalars; the expected number of restarts restores \(\Theta(\sqrt{q})\) nodes.

**Costs.** \(\Theta(\sqrt{q})\) support terms, \(\Theta(\sqrt{q})\) memory, \(O(\log q)\) verification on a constant number of false hits, no advice beyond the curve. Negation and interleaving, their Sections 4.1–4.3, change the constant inside the same list size.

**Prior art read this session.** Liao–Zhang, Algorithms 1–4, equations (17)–(18), Remarks 1–3, and the start of Lemma 1. The H021 EDS screen is the in-repo comparator; this card only adds the genealogy count for the lazy reading that screen left open. Not a new schedule and not layout B.

**Unsupported assumption.** That some subtree, or some reuse of one \(h_{2\ell}\) across a positive-density set of parents, emits a cover of \(k\) with \(o(\sqrt{q})\) distinct support indices. The parent map of (17)–(18) does not do that.

**Falsifier.** Already a count: \(N\) emitted baby indices in a tree of out-degree at most \(2\) require \(\Theta(N)\) nodes, and distinct parents have distinct even support indices. Reopen only with a recurrence whose support set is \(o(\sqrt{q})\) on a positive-density set of \(k\), with that set priced against the x-only expression above.

## 3. Relative quadratic character of \(W(k)\) against its absolute sign

**Public computation.** From the corrected mask,
\[
\frac{W(k+1)}{W(k)}=\frac{\varphi(Q+G)}{\varphi(Q)}\,\gamma^{-(2k+1)}.
\]
The exponent \(2k+1\) is odd, so
\[
\Bigl(\frac{W(k+1)/W(k)}{p}\Bigr)
=\Bigl(\frac{\varphi(Q+G)/\varphi(Q)}{p}\Bigr)\Bigl(\frac{\gamma}{p}\Bigr)
\]
is independent of \(k\). The same holds one step at a time. The relative window of Legendre symbols around the unknown index is therefore public, at one \(\varphi\)-evaluation per step. This is Lauter–Stange, Proposition 4, rewritten with the \(n^2\) mask.

The absolute symbol \((W(k)/p)\) is not public. If \((\gamma/p)=-1\),
\[
\Bigl(\frac{\varphi(Q)}{p}\Bigr)=\Bigl(\frac{\gamma}{p}\Bigr)^{k}\Bigl(\frac{W(k)}{p}\Bigr)
\]
ties that symbol to the parity of \(k\). One equation, two unknowns. Their Remark 1 in Section 7 replaces \(G\) by a small multiple so that the base \(\varphi\)-value is a non-residue when \(-1\) is a non-residue; that changes the generator and does not split the equation.

**Recovery, if the sign were known.** Their Proposition 2: \(q\) odd makes halving unique, each halving is multiplication by the public scalar \(2^{-1}\), and \(\log_2 q\) parity bits assemble \(k\). Their Proposition 3 turns the absolute symbol into the parity bit precisely when the base is a non-residue. Total, after the bits are known, is \(O((\log q)^2)\) field operations plus the net cost of the \(\varphi\) values.

**Gain.** Polynomial complete work, and only then. The second view that would pin the sign is missing. A global bias \(\mu\) of \((W(n)/p)\) along known indices would do it: known indices are cheap, \(O(\log n)\) net operations each, and a window of length about \(1/\mu^2\) distinguishes the true sign from its flip. Lauter–Stange Section 8 record that they have no evidence \(\mu\neq 0\). If \(\mu=0\), or if \(|\mu|\ll q^{-1/4}\), the window is already longer than a rho run.

**Costs.** Preprocessing is \(N\) known-index symbol evaluations, charged. Online cost is \(\log q\) windows. No list of points. If the test returns the wrong sign, halving follows a wrong branch and the final scalar check fails; that trial is charged in full. No hidden advice.

**Prior art read this session.** Lauter–Stange, Propositions 2–4 and Sections 7–8. This is not the H022 cubic square-class, which is identically \(1\) on rational points, and not an auxiliary Tate residue. H003 and H014 average characters of point functions; they were not re-run and are not this index sequence.

**Unsupported assumption.** That \((W(n)/G)\) has a bias large enough that a window shorter than \(\sqrt{q}\) identifies the sign, on an ordinary prime-order curve, after the base point is moved so that \((\varphi/p)=-1\).

**Falsifier, not run.** One ordinary curve with \(q\) prime near \(2^{12}\) and \(\gcd(q,p-1)=1\). If no base \([n]G\) with \(n<q\) has \((\varphi([n]G)/p)=-1\), the parity route does not start. Otherwise compute the mean of \((W(n)/p)\) over all nonzero indices, or over \(N\ge 10^4\) known indices if a full pass is refused. Kill the card if \(|\mu|<10/\sqrt{q}\), or if a length-\(32\) window does not rank the true sign above its flip by more than a random \(\pm 1\) sequence. A pass at this size would still not be an asymptotic claim.

## What this pass does not reopen

Fixed-progression layouts, centered multipliers, fixed-difference reversal, translation indexes, the dyadic \(S_3\) product, orbit-sum endpoint formulas, auxiliary Tate residues at \(\ell\neq q\), and signed layout B. Tangent-slope collisions add fibers and worsen the useful-hit ratio. The chart \(z=-x/y\) is not linear in \(k\): the formal group law has higher terms, and a homomorphism \(E(\mathbb{F}_p)\to\mathbb{F}_p^\times\) is trivial under \(\gcd(q,p-1)=1\).

No short circuit, no new detector, and no pair of public views with an independent recovery constraint came out of these three constructions.
