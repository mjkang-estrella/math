# H008 recent-source scouting: raw Grok report

Provider grok, model grok-4.7, request
ecdloop-h008-recent-mechanisms-grok-20261008-r1. Completed, no experiment.
Raw report is NOT accepted as theorem evidence. Root objections:
- Public dependence does not imply scalar information is absent: Q itself is public.
- Containment in a large torsion field does not prove a large evaluation cost.
- A sufficient congruence for a limit is not an unconditional computational lower bound.
- Frobenius polynomial discriminant need not equal the endomorphism-order discriminant.
- Isogeny degree is not evaluation work; Frobenius itself demonstrates this.
- pi(R)=R does not imply pi(R)=[n]R for general n. The displayed zero-identity
  argument is restricted to comparing pi with identity, not arbitrary [n].
No pilot is justified, but these incorrect universal obstructions are rejected.
Primary links are scouting leads, not a root-verified exhaustive literature survey.

No 2024–2026 primary source examined here supplies a paid classical operation below negation-rho on an ordinary prime-field prime-order curve. Verified improvement remains **NONE**. Three candidate operations were read out of those sources; each fails its full-work threshold on the stated hypotheses, so none is proposed for a pilot.

The working reference is unchanged: one full scalar, only negation, expected about \(\sqrt{\pi q/4}\) group operations, with preprocessing, memory, failed trials, empty outputs, and extraction charged. Shoup’s generic bound does not exclude a coordinate method. No experiment was run.

Mahalanobis, arXiv:2607.09814, was not reviewed. Quantum-circuit papers were excluded. An arXiv query for the phrase “elliptic curve discrete logarithm” over 2024-01-01 through 2026-12-31 returned 19 hits; aside from that excluded paper, they are quantum. This is not a certificate that the literature search was exhaustive.

## Scoped sources

**Bhakta–Shparlinski, correlation averages.** Theorem, not an algorithm. [arXiv:2507.09271v1](https://arxiv.org/abs/2507.09271v1) (12 Jul 2025). For \(\chi\) of order \(d\), \(R=d\cdot\mathrm{ord}(P)\), and
\[
S_{\chi,P}(N,h)=\sum_{n=1}^{N}\chi(\psi_n(P))\chi(\psi_{n+h}(P)),
\]
Theorem 1.2 bounds the shift-averages \(U_{m,\chi,P}(H,N)\) and \(V_{m,\chi,P}(H,N)\) by
\[
H^{-1/8}R\exp\bigl(O((\log R)^{1/2}/\log\log R)\bigr)+H^{1/2}R^{3/4}p^{1/8}\log R,
\]
and, when \(R\ge p^{1/2}\exp(2.1\log p/\log\log p)\), by \(H^{-1/4}R^{7/6}p^{1/24}(\log R)(\log\log R)^{1/6}\). Question 1.1, the pointwise claim \(S=o(N)\), is stated as open. The authors call the gap between the two nontrivial ranges a multiple of \(p^{1/2}\). Lemma 2.1, the almost-multiplicative law \(\chi(\psi_{mn}(P))=\chi(\psi_m(nP))\chi(\psi_n(P))^{m^2}\), is quoted from Shparlinski–Stange, not proved as a new ECDLP reduction.

For quadratic \(\chi\) and \(q\sim p\), one has \(R\sim 2p\). The second term of (1.3) is already \(\Omega(p^{7/8})\) for every \(H\ge 1\), so a direct sum is nontrivial only for summation length above \(p^{7/8}\). Bound (1.4) is nontrivial only for \(H\gtrsim p^{5/6}\) and sums of length comparable to \(R\). Both sit above \(\sqrt p\).

**Bhakta, twisted division sums.** Theorems, same negative direction. [arXiv:2508.03988v2](https://arxiv.org/abs/2508.03988v2) (9 Aug 2025); journal version [Canadian Mathematical Bulletin, DOI 10.4153/S000843952610191X](https://doi.org/10.4153/S000843952610191X). With the same \(R\):

- Theorem 1.1: a \(\tau_\nu\)-bounded twist saves only \((\log\log R)^\nu/\log R\) once \(N\ge p^{1/12}R^{5/6+\varepsilon}\). The quadratic-character remark extends the lower end only to \(N\ge p^{1/2+\varepsilon}\).
- Theorem 1.2: a fixed Dirichlet twist is \(\ll p^{1/12}R^{5/6}(\log R)(\log\log R)^{1/3}\), about \(p^{11/12}\) when \(R\sim p\).
- Theorem 1.3: the \(\mu^2\) twist is nontrivial only for \(N\gg p^{11/12}\) in that same range.
- Theorem 1.4: the smooth-integer twist is nontrivial only for \(N\gg y^3 p^{1/12}R^{5/6}\) with \(y\) as small as \(p^{1/36}\), hence still \(N\gg p^{11/12}\).

These are upper bounds. Smallness of \(\sum f(n)\chi(\psi_n(P))\) does not name \(k\). The proved ranges start at or above square-root length, and the summand count is the cost.

**Stange, isogeny division polynomials.** Theorems about functions, not a search. [arXiv:2503.15428v3](https://arxiv.org/abs/2503.15428v3) (17 Apr 2026); journal [Res. Number Theory 12, 53 (2026), DOI 10.1007/s40993-026-00741-2](https://doi.org/10.1007/s40993-026-00741-2). Also [ePrint 2025/521](https://eprint.iacr.org/2025/521). Division polynomials \(\Psi_\phi\) are defined for isogenies whose kernel need not sum to the identity, by replacing the Mazur–Tate divisor with \(\phi^*(O')-(\deg\phi)(O)+(P_\phi)-(O)\). Theorem 5.1 is an \(x\)-coordinate parallelogram law for two isogenies. The second recurrence and chain rule are the analogues of the classical division recurrence. Theorem 6.3 says that \(\Psi_{\sum a_i\phi_i}(P)\), for isogenies \(\phi_i:E\to E'\), form an elliptic net attached to the points \(\phi_i(P)\).

On \(E(\mathbb F_p)\), Frobenius acts as the identity. For an ordinary curve the non-scalar endomorphisms have degree at least \(|\Delta|/4=(4p-t^2)/4\), and Frobenius itself has degree \(p\). Neither evaluation is an \(o(\sqrt q)\) operation on a large-discriminant prime-order curve.

**Katagiri–Kobayashi, \(p\)-adic limits.** Theorem identifying a limit, not a discrete-log extraction. [arXiv:2609.07024v1](https://arxiv.org/abs/2609.07024v1) (7 Sep 2026). Theorem 1.3: for good reduction, \(P\in E(K)\setminus\hat E(K)\), and \(r=p^j r'\) the order of the reduction of \(P\), a power \(q=p^N\) gives
\[
\lim_{k\to\infty} F_{m q^k}(P)
\]
equal to a ratio of Mumford’s algebraic sigma at the Teichmüller lift of the prime-to-\(p\) part of that reduction, or to \(0\) if \(r\) is a \(p\)-power. The stated sufficient \(N\) satisfies \(p^N\equiv 1\pmod{2r'^2 h}\). Proposition 2.5 places \(\sigma^{\mathrm{alg}}(\widetilde T)\) in \(K(E[4N^2])\). Corollary 1.4: the limit is algebraic over the Weierstrass field and vanishes if and only if \(r'\mid m\).

For an \(\mathbb F_p\)-point of order \(q\nmid p\), the right-hand side is fixed by the public reduction. The limit deletes the formal-group component. Silverman’s older periodicity statement, the antecedent for finite fields, is Corollary 9 of [math/0404412](https://ar5iv.labs.arxiv.org/html/math/0404412): \((F_n(P))\) is purely periodic of period \(rt\) with \(t\mid(q-1)\) or \(t\mid 2(q-1)\).

**Gezer–Bizim, translated sequences.** Abstract-level only; the identities were not rederived. [arXiv:2607.11261v1](https://arxiv.org/abs/2607.11261v1) (13 Jul 2026). The abstract’s finite-field claim is pure periodicity of translated division values \(\Psi_n,\Phi_n,\overline\Omega_n\) at a pair of points, then a \(\mathbb Z_p\)-Cauchy subsequence and the same for Somos 4 and 5. Periodicity of a sequence built from public points recovers a period tied to the public order, which is already known.

**Non-transfers, scoped from their hypotheses.**

- Lido, [arXiv:2206.10327v2](https://arxiv.org/abs/2206.10327v2) (22 Feb 2025), Theorem 1.1: probabilistic quasi-polynomial time for the multiplicative group of a finite field of small characteristic, meaning cardinality \(p^n\) with \(n>p\). That is a field-DLP theorem in small characteristic. It does not apply to \(\mathbb F_p^\times\) or to \(E(\mathbb F_p)\).
- Bollauf–Parisella–Siim, [ePrint 2025/1079](https://eprint.iacr.org/2025/1079), [DOI 10.62056/a0c3c3c2h](https://doi.org/10.62056/a0c3c3c2h). Abstract only. The reduction runs from a smooth-\((p-1)\) discrete log to CDH, n-PDL, and n-DHE. That is evidence that CDH is as hard as DL, not an algorithm for DL.
- Otsubo, [arXiv:2610.03100v1](https://arxiv.org/abs/2610.03100v1) (2 Oct 2026). Degree-3 Hesse isogenies and a Serre–Tate description of the canonical lift in characteristic 3. Characteristic 3 and a canonical-lift identity are outside ordinary large prime-order ECDLP.
- Higher-dimensional isogenies. H004 already recorded that Robert’s direct interpolation needs auxiliary torsion and the unknown isogeny’s images on it ([breaking SIDH, Theorem 1.1](https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/articles/breaking_sidh.pdf)). No 2024–2026 paper found in this pass removes that input for an ordinary prime-order curve. Supersingular endomorphism-ring algorithms remain supersingular.

Dense tensor schedules, norm-walk scans, and the frozen carry-LP circuit stay lost. None of the operations below is one of those three.

## Three candidate operations

Each card is the natural reading of one source. All three are rejected before any pilot.

**1. Direct shifted division-character summation.** Evaluate \(\chi(\psi_n(P))\) by the division recurrence and average \(|S_{\chi,P}(N,h)|\) as in Bhakta–Shparlinski. The different operation from a group walk is the character of the division value at the integer index \(n\), not a collision of points. Proposed gain: none inside the proved range. For \(R\sim p\) the nontrivial window already asks for length \(\Omega(p^{7/8})\) or for \(\Omega(p^{5/6})\) shifts of full-period sums. Prior art is Shparlinski–Stange’s bound, nontrivial only for \(N\ge p^{1/2+\varepsilon}\). Unsupported assumption would be a \(k\)-dependent shift with \(|S|\ge\Delta N\) at \(N=o(\sqrt q)\). Question 1.1 does not assert that, and the proved statements are upper bounds. Full-work threshold: summation length \(o(\sqrt q)\), including every \(h\) tested and every zero term. Cheap falsifier: substitute \(R=2q\), \(q\sim p\), into (1.3) and (1.4). The right-hand side drops below the trivial size \(N\) only for \(N\) or \(H\) above \(\sqrt p\). A single small prime where a short sum happens to be large would not refute the asymptotic range.

**2. Algebraic-sigma limit of a \(p\)-power subsequence.** Lift a public point, form \(F_{m p^{Nk}}(P)\) until the Katagiri–Kobayashi limit, and read a ratio of sigma values. The different operation from carry-LP is this explicit limit, not a relaxed circuit. Proposed gain: none. Theorem 1.3’s right-hand side depends on the Teichmüller lift of the reduction, which the public point already determines, and the formal component is erased, so the hidden scalar is not in the output. Prior art is Silverman’s Theorem 12, which gave existence of the limit in the ordinary case without identifying it. Unsupported assumption would be a compatible lift with \(\mathrm{lift}(Q)=[k]\mathrm{lift}(P)\) whose formal discrepancy survives the limit. The identity says it does not. Full-work threshold: \(o(\sqrt q)\) field operations, including construction of any value in \(K(E[4q^2])\) and every failed precision. Cheap falsifier: Proposition 2.5 places one sigma value in \(K(E[4r'^2])\). For \(r'=q\) that is the \(4q^2\)-torsion field. Separately, the paper’s sufficient exponent already solves \(p^N\equiv 1\pmod{2q^2 h}\). Either demand is above \(\sqrt q\). This is a theorem-level obstruction for this formula, not a claim that every \(p\)-adic function is useless.

**3. Endomorphism-net evaluation on rational points.** Use Stange’s recurrence or Theorem 5.1 at \(\alpha=\pi\) and \(\beta=[n]\). The different operation from the H006 Somos schedule is the biased-kernel divisor \(\phi^*(O')-(\deg\phi)(O)+(P_\phi)-(O)\). Proposed gain: none on \(E(\mathbb F_p)\). Frobenius and an integer induce the same map on rational points, so Theorem 5.1 has right-hand side \(x(R)-x(R)=0\), and \(\pi-\mathrm{id}\) kills every rational point, which makes the identity \(0=0\). Theorem 6.3 then attaches the net to a repeated point, so the rank drops to the classical one-point net. A genuinely non-scalar endomorphism has degree \(|\Delta|/4\) or \(p\), and writing its kernel is already heavier than negation-rho when \(|\Delta|\gg\sqrt q\). Prior art is the classical division recurrence and the elliptic net of rank equal to \(\mathrm{rank}\,\mathrm{End}(E)\) only after the isogenies are distinct on the point. Unsupported assumption would be an \(\mathbb F_p\)-rational endomorphism of degree \(o(\sqrt q)\) other than \(\mathbb Z\). Full-work threshold: one such evaluation, kernel included, in \(o(\sqrt q)\) operations on a curve with \(|\Delta|>4\sqrt q\). Cheap falsifier: on any rational point, \(\pi(R)=R\), so the two isogenies in Theorem 5.1 are not independent labels. That is the same missing-label collapse already recorded for parallel chords, now read off Stange’s identity rather than off a new walk.

No fourth operation in this pass had a concrete cost below the baseline. Pointwise short division-character sums remain an open analytic question; a future bound in that direction would be another cancellation statement, still not a construction of \(k\).
