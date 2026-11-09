# H008 — Audit of the single-embedding quadratic resultant selector

Date: 2026-10-07 America/Los_Angeles / 2026-10-08 UTC.
Assigned source: [W001 relations, Card C](../hypotheses/W001-relations.md), read in full, and [W001 baselines](../hypotheses/W001-baselines.md).

**Disposition: reject the specified very thin single-embedding selector as a source of the relation population assumed by Card C.** There is an elementary, distribution-free counting obstruction: if

\[
72\epsilon H^4<1,
\]

at most **one primitive irreducible quadratic, up to sign**, of height at most H can satisfy

\[
|g(\alpha)|\le\epsilon H(1+|\alpha|+|\alpha|^2)
\tag{1}
\]

at a fixed real or complex number \(\alpha\). The proof below uses an integer resultant and works even for specially correlated roots. With the proposed H, d and tolerances, this inequality holds for all sufficiently large N. Taking the union over the roots of one degree-d polynomial therefore supplies at most d distinct admissible quadratics; the three nested tolerances do not multiply that count. This is far below the \(L_N[1/3,b]\) population required by the proposed conventional relation-collection model.

This is an **informal proved restricted counting lemma, pending independent review**, not a formally verified result, a general small-resultant obstruction, or a lower bound for factoring. Verified new factoring improvement: **NONE**. No finite counting experiment, factoring run, lattice search, siever, or Lean change was performed. No claim is promoted by this report.

## 1. Scope and analytic protocol

Only this report and the named provenance scratch file `H008-resultant-provenance.json` are owned by this pass. The project instructions, README, specification, research loop, team rules and checkpoint were read. The user's narrower report-only assignment controls; shared code, shared state, other children's reports, packages, commits, publication, scheduling and delegation are outside this pass.

The fixed question is whether Card C's explicitly proposed r = 3 slab can retain sufficiently many primitive irreducible sieving elements after every scan and rejection is counted. We audit that selector, rather than assume a small-resultant tail can be sampled for free.

The parameter family is

\[
t=\log N,\qquad \ell=\log t,\qquad
H=\exp((a+o(1))t^{1/3}\ell^{2/3}),\qquad
B=\exp((b+o(1))t^{1/3}\ell^{2/3}),
\]
\[
d=(\delta+o(1))(t/\ell)^{1/3},\qquad
\epsilon_\lambda=N^{-\lambda/d},\quad
\lambda\in\{1,3/2,2\},\qquad a,b,\delta>0.
\]

Use integer-rounded H and d, with d at least 3. Let f be the monic irreducible base-m polynomial under consideration, with f(m) = N, height A = O(m), and \(\log m=(1+o(1))t/d\). The counting lemma does **not** need f, irreducibility of f, algebraicity of the tested point, or the base-m property. Those hypotheses are needed only to interpret norms and specify certified membership tests economically. Cases where base-m construction is nonmonic or reducible require their usual separate processing; this report does not assume they establish a new N-only factoring algorithm.

The analytic rejection criterion is an upper bound of poly(t) distinct retained irreducible elements for a fixed f, contradicting this selector's intended \(L_N[1/3,b]\) relation-population premise. A lack of a generic volume estimate alone would have been inconclusive.

**Experimental decision:** no finite probe is mathematically needed, because the exact resultant argument establishes that bound for the whole stated asymptotic family. Experiment allocation in this pass: **0 seconds; no trials or seeds**. Any later probe needs its own frozen concrete inputs, exact arithmetic protocol, rejection rule and hard cap of at most **60 seconds before execution**. No preregistration is retroactively claimed for the mathematical derivation here. The negative result and input/report hashes are retained; there are no omitted failed or censored experimental trials.

## 2. One explicit, fully enumerable selector

Define the real-embedding selector as follows. A dyadic outward relaxation makes every membership comparison exact over the field containing the root; it only makes the rejection stronger.

1. Construct f and isolate all its real roots by a certified integer-polynomial root-isolation algorithm. An embedding is an isolating rational interval together with f, not a floating-point approximation.
2. For \(\lambda=p/q\) in the fixed list, set
   \[
   k_\lambda=\left\lfloor\frac{p\log_2N}{qd}\right\rfloor,
   \qquad E_\lambda=2^{-k_\lambda}.
   \]
   Compute k using the exact comparisons
   \(2^{kqd}\le N^p<2^{(k+1)qd}\), without computing a numerical logarithm. Thus \(\epsilon_\lambda\le E_\lambda<2\epsilon_\lambda\). The largest tolerance is E_1.
3. Scan every integer tuple \((a_0,a_1,a_2)\in[-H,H]^3\) once, in lexicographic order. Every visited tuple contributes to the scan count, including zero, imprimitive, reducible, wrong-sign and failed-slab tuples. Keep only a2 > 0 and \(\gcd(a_0,a_1,a_2)=1\). Reject reducible quadratics by the exact discriminant test: \(a_1^2-4a_2a_0\) must not be a nonnegative integer square.
4. For each real root \(\alpha_j\), decide (1) with E_1 in place of epsilon. The smaller two tolerances can be recorded as tags; they never add candidates. Retain a polynomial once if it passes at any root. Optionally compute its exact rational image g(m) and integer resultant Res(f,g). No smoothness, ideal-vector, rank or factor-extraction success is inferred from admission.

This is deliberately the complete cube enumeration allowed by Card C. It uses **no lattice enumeration or short-vector oracle**. Its exact raw scan count is

\[
M=(2H+1)^3;
\]

there are at most dM widest-slab comparisons, or at most 3dM if all tolerance tags are evaluated. It can stream tuples and retain only the accepted list and provenance. No output-sensitive running time is claimed.

### Certification and bit cost of membership

For a real root with sign s, the slab is equivalent to both inequalities

\[
Q_\pm(\alpha)\ge0,\qquad
Q_\pm(X)=H(1+sX+X^2)\pm2^k g(X).
\tag{2}
\]

These are integer polynomials of degree at most 2 and height at most \(K=(2^k+1)H\). Detect an identically zero Q first. Every other Q is coprime to the irreducible f of degree greater than 2. Put R = A + 1, a Cauchy bound for all roots of f. Since

\[
1\le|\operatorname{Res}(f,Q)|
=\prod_{i=1}^d|Q(\alpha_i)|,
\qquad |Q(\alpha_i)|\le3KR^2,
\]

each individual nonzero evaluation satisfies

\[
|Q(\alpha_j)|\ge (3KR^2)^{-(d-1)}.
\tag{3}
\]

On a real interval inside [-R-1,R+1], \(|Q'|\le5KR\) for R at least 2. Refining a certified isolating interval to width less than

\[
\frac{(3KR^2)^{-(d-1)}}{10KR}
\]

therefore determines its sign by rational evaluation with a rigorous error bound. Required precision is \(O(d(k+\log H+\log R))\) bits, polynomial in the binary input length and the supplied polynomial data. Equality cannot be hidden by a near-zero floating evaluation: it was handled by Q identically zero or excluded by coprimality. Standard certified isolation/refinement gives polynomial bit work at this precision; this is an algorithmic overhead, not free access to real roots. [Sagraloff–Mehlhorn, Theorems 2–3 and their root-refinement discussion](https://arxiv.org/pdf/1308.4088v2).

Base-m expansion, computing the integer dyadic exponents, and gcd/discriminant checks all have polynomial bit cost. No irreducibility oracle is needed to enumerate: for a general monic f, first take its square-free part by polynomial gcd. For each nonzero Q, compute the monic gcd D of f and Q. Its roots give exact zero evaluations, identifiable by certified isolation/refinement; on the remaining roots apply (3) to the monic integer polynomial f/D, using its actual degree and height. Polynomial gcd and the resulting coefficient sizes have polynomial bit bounds. This also charges the zero-evaluation cases that the irreducible branch excludes. Interpreting the results as relations in one number field still requires the irreducible f assumed in Section 1; the enumeration itself can simply report its candidates without claiming to factor N.

With \(P=\operatorname{poly}(n,d,\log A,\log H,k)\), n the bit length of N, the explicit selector has

\[
T_{\rm select}\le P+(2H+1)^3dP
=L_N[1/3,3a],
\tag{4}
\]

where the last equality denotes its asymptotic upper cost scale, suppressing polynomial factors. The scan also performs M tuple visits, regardless of how few points qualify. Streaming workspace, certified root data and the admitted list are polynomial-size under the counting bound below. Computing all admitted g(m) and Res(f,g) is an additional polynomial factor per admitted element: integer Sylvester determinants can be computed by exact fraction-free elimination with polynomial operand widths. No full factorization of these integers is part of (4).

The following proof also bounds a complex-disk selector, without needing to build one. A different enumerator, including a correlated lattice enumerator, cannot create more members of the same defined set.

## 3. Exact separation lemma: thin windows collapse to common factors

**Lemma.** Let g and h be integer polynomials of degree exactly 2 and coefficient height at most H, with nonzero constant terms. Suppose both satisfy (1) at the same \(\alpha\in\mathbb C\). Then

\[
|\operatorname{Res}(g,h)|\le72\epsilon H^4.
\tag{5}
\]

Consequently, if \(72\epsilon H^4<1\), g and h have a common factor over Q. If both are primitive and irreducible, they are equal up to sign.

**Proof.** First suppose \(|\alpha|\le1\), put \(z=\alpha\), and write \(g=c_0+c_1X+c_2X^2\), \(h=e_0+e_1X+e_2X^2\). The matrix

\[
S=\begin{pmatrix}
c_0&c_1&c_2&0\\
0&c_0&c_1&c_2\\
e_0&e_1&e_2&0\\
0&e_0&e_1&e_2
\end{pmatrix}
\]

has determinant equal to the resultant, up to an irrelevant sign. Replace its first column by the first column plus z times the second, z squared times the third, and z cubed times the fourth. The determinant is unchanged; the new first column is

\[
(g(z),\;zg(z),\;h(z),\;zh(z))^{\mathsf T}.
\]

Each entry has magnitude at most \(3\epsilon H\). Each complementary 3 by 3 minor has magnitude at most \(6H^3\), by expanding its determinant into six products. Expansion along the new first column yields \(4\cdot3\epsilon H\cdot6H^3=72\epsilon H^4\).

If \(|\alpha|>1\), put \(z=1/\alpha\), \(g^*(X)=X^2g(1/X)\), and similarly for h. Both reversed polynomials are degree 2 with height at most H. They satisfy

\[
|g^*(z)|=|g(\alpha)|/|\alpha|^2
\le\epsilon H(1+|z|+|z|^2)\le3\epsilon H,
\]

and the same for h. Apply the preceding determinant argument to g* and h*. Reversing both binary quadratic forms preserves the magnitude of their resultant. Equivalently, their Sylvester matrices differ by row and column permutations. This proves (5) also in this case.

The resultant is an integer. Magnitude strictly less than 1 forces it to be zero. Two genuine quadratics with zero resultant share a nonconstant factor. Two irreducible quadratics must consequently be proportional over Q, and primitive integral coefficients make the proportionality factor +1 or -1. This proves the lemma. No equidistribution, root separation hypothesis for alpha, smoothness heuristic, or volume-to-point approximation occurs in the argument. □

**Corollary for the explicit selector.** Irreducible quadratics have nonzero constant terms. Therefore if \(72E_1H^4<1\), at most one admitted polynomial has a given witnessing root. There are at most d roots, so the union contains at most d distinct polynomials. Positive leading coefficient removes the sign duplication. Conjugate complex embeddings have identical absolute-value conditions for real coefficient polynomials, so counting both separately only weakens this upper bound. The condition holds, for example, whenever \(144\epsilon_1H^4<1\).

This also covers adversarially chosen f and roots very close to a low-height quadratic root. Such a correlation can preserve one exceptional irreducible polynomial in an arbitrarily thin slab; it cannot preserve many different irreducible quadratics in that same slab at this height. Allowing many lattice windows at a fixed embedding, while preserving (1) and H, does not change that fact.

## 4. Scale correction, volume audit, and the large-root challenge

For the stated degree,

\[
\log(1/\epsilon_\lambda)=\lambda t/d
=(\lambda/\delta+o(1))t^{2/3}\ell^{1/3}.
\tag{6}
\]

The \((\log\log N)^{1/3}\) factor **multiplies**, rather than divides, \((\log N)^{2/3}\). This corrects the expression in the parent tentative objection without changing its conclusion. In particular,

\[
\frac{\log(1/\epsilon_\lambda)}{\log(H^3)}
\sim\frac{\lambda}{3a\delta}(t/\ell)^{1/3}\longrightarrow\infty.
\]

Thus \(\epsilon_\lambda H^C\to0\) for every fixed C. The exact rejection condition from Section 3 eventually holds for all three proposed tolerances, for every fixed positive a and delta. No numerical threshold or finite-size crossover is asserted.

For comparison, the continuous-volume calculation is straightforward. For a real alpha, write \(v=(1,\alpha,\alpha^2)\), \(S_\alpha=1+|\alpha|+|\alpha|^2\), and choose a coordinate with \(|v_i|=\|v\|_\infty\ge S_\alpha/3\). Conditional on the other two continuous coordinates, (1) restricts that coordinate to an interval of length at most \(6\epsilon H\). The uniform continuous acceptance fraction is therefore at most \(3\epsilon\). If one **assumes** comparable generic discrete density, the inverse selection fraction is of scale

\[
L_N[2/3,\lambda/\delta],
\]

not \(L_N[1/3,\tau]\) with fixed tau. Formally forcing it into the latter notation requires

\[
\tau_N=(\lambda/\delta+o(1))(t/\ell)^{1/3}\to\infty.
\]

The modeled population \(O(\epsilon H^3)\) tends to zero. This is **not** a rigorous discrete count: a slab can contain exact or extraordinarily close algebraic directions even when its volume tends to zero. The rigorous replacement here is the one-irreducible-polynomial bound, not a claim that the slab is empty or that its actual discrete acceptance fraction equals epsilon. It would be wrong to apply the continuous density at one point in the argument and then count exceptional correlated survivors as though they had that density.

There is also a simple, independent large-root obstruction. If \(|\alpha|=R\ge2H+2\) and \(a_2\ne0\), then

\[
|g(\alpha)|\ge R^2-HR-H>R^2/2,
\qquad H(1+R+R^2)\le3HR^2.
\]

Consequently no such g satisfies (1) when \(\epsilon<1/(6H)\). This proves the claimed inability to cancel the leading term at a sufficiently large root, conditionally on that root's size. It does **not** assert that every base-m polynomial has a real root of size approximately m. For example, the elementary trace bound guarantees only \(\max_i|\alpha_i|\ge|c_{d-1}|/d\); when \(|c_{d-1}|\ge\kappa m\) for fixed kappa > 0, it does guarantee at least one embedding too large for this selector asymptotically. Other coefficient patterns require their own argument. Section 3 did not need any large root at all.

## 5. Norm gain is real as a bound, but the population is missing

Let \(M(f)=\prod_i\max(1,|\alpha_i|)\) be the Mahler measure of the monic f. The standard coefficient inequality \(M(f)\le\|f\|_2\le\sqrt{d+1}\,A\), together with \(1+u+u^2\le3\max(1,u)^2\), gives the deterministic upper bound

\[
|\operatorname{Res}(f,g)|
\le (3H)^d(d+1)A^2.
\tag{7}
\]

For completeness, the first inequality follows by averaging \(\log|f(e^{i\theta})|\) on the unit circle, applying concavity of log to its squared absolute value, and using Parseval's identity. No typical-size assertion is needed.

Passing a single real-root slab improves this bound by a factor E_lambda, since that one root factor is reduced by that amount. A complex disk improves it by \(E_\lambda^2\), because the conjugate factor is reduced too. The rational-side bound remains

\[
|g(m)|\le H(1+m+m^2)\le3Hm^2.
\]

Hence, at the level of upper norm scales, a real-root slab replaces the algebraic term \(2t/d\) by \((2-\lambda)t/d\), corresponding to \(\eta=1-\lambda/2\) in Card C. The three nominal eta values are 1/2, 1/4, and 0. A dyadic factor less than 2 changes only a lower-order term. This calculation explains the attraction of the proposal; it does not supply relation density or smoothness independence.

Under Card C's **conditional** no-selection-loss, usual-smoothness and usual-completion-cost assumptions, optimizing its inequalities gives

\[
c_{3,\eta}^{\,3}=\frac{128(1+\eta)}{27}.
\]

The cited Coppersmith comparison has

\[
c_C^3=(92+26\sqrt{13})/27,
\]

so its conditional threshold is indeed \(\eta<(92+26\sqrt{13})/128-1\), approximately 0.4511. This is a **leading-constant comparison within exponent 1/3**, not a smaller L exponent or polynomial time. The exact Coppersmith constant is stated in [Lee–Venkatesan, Remark 4.31](https://arxiv.org/html/1805.08873v1); the [original Coppersmith primary record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve) confirms the multiple-polynomial modification.

The present selector fails before that optimization can apply: it offers at most d distinct irreducible elements for each f even if every one is smooth and generation were free. Thus replacing its cost by a finite fixed tail penalty tau is not a valid repair of the desired large-population assumption. The lemma does not exclude isolated unusually good relations, or a lucky factor from a tiny set of relations, but neither is the population or success guarantee claimed by the original heuristic calculation.

## 6. Remaining costs, rank, and limits of the rejection

If one nevertheless runs the explicit cube scan on J different defining polynomials, charge at least J separate setup costs and J M tuple visits for that implementation, with root tests and exact arithmetic as in (4). The union has at most Jd accepted irreducible elements before smoothness filtering and relation deduplication. Reaching the original target of \(L_N[1/3,b]\) distinct rows therefore needs at least \(L_N[1/3,b]/d\) such defining polynomials even under perfect acceptance. A different generator might reuse computations; it must specify and price that reuse. Extra fields also change ideal bases and dependency/root reconstruction, precisely the kind of accounting already present in multiple-polynomial NFS. This report does not claim a lower bound on all multiple-field methods.

For any claimed factoring continuation, (4) is only the selector charge. The full ledger is

\[
P_{\rm fields}+T_{\rm select}+T_{\rm rational/ideal\ bases}
+T_{\rm smooth/ideal\ processing}+T_{\rm filtering}
+T_{\rm sparse\ algebra}+T_{\rm algebraic\ roots}+T_{\rm gcd/restarts}.
\]

Even if rational primes are bounded by B, distinct prime ideals must be recorded separately. Away from the index/discriminant exceptions, an ideal dividing a primitive quadratic element can have residue degree up to 2, since its residue polynomial divides g modulo p. There are at most d prime-ideal factors above each p, so the potential good-prime column count is at most \(d\pi(B)\), plus rational, sign, exceptional and character columns. This is an upper count, not a free algorithm for all exceptional data. Integer norm parity is not sufficient for an algebraic square. The need for ideal information and additional square conditions is explained in [Stevenhagen, Sections 4–10](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).

With D columns and W nonzeros, using the usual sparse linear-algebra estimate requires roughly \(\widetilde O(DW)\) bit work and charged storage/provenance. It does not prove the rows are independent, give an algebraic square root, or give a proper factor. A new sampling bias still needs a lower bound on useful splitting probability \(\sigma_N\), with complete restart cost divided by that probability. No such probability is established here. At most d admitted polynomials yields at most d distinct rows, regardless of their putative smoothness; it cannot guarantee the conventional B-scale collection. Some small matrices can have dependencies, so B rows are not asserted to be a universal necessity for every factoring mechanism.

Dropping primitive normalization only adds integer multiples and scalar square classes with their own factorization costs. Dropping irreducibility admits products of linear elements. For \(g=uv\), both g(m) and the algebraic element factor multiplicatively, their ideal/sign/character vectors add, and their norms multiply. Thus an already processed pair u,v gives no new relation direction from its product. This does **not** prove that every reducible family has bounded relation rank: new linear factors can supply new directions, and their generation, height, smoothness and rank must be counted. The present theorem deliberately rejects the irreducible quadratic selector; it does not quietly substitute coefficient-space rank for rank over the binary ideal matrix.

The proof is uniform over the embedding, but restricted to degree 2 and the very small single-embedding tolerance. It leaves open different height regimes, changing degree, distributed norm reduction across many embeddings, or other correlated constructions. No balanced multi-embedding lattice family is constructed or endorsed in this pass. To become a candidate, such a revision must first supply its actual integer lattice/basis and determinant, an admissible height region, certified enumeration including all short-vector search costs, a lower count of distinct useful elements, and simultaneous rational/norm bounds. Merely writing a balanced embedding box is not that construction. Any revision still imposing (1) at one embedding at the current height inherits this rejection.

## 7. Checked primary prior art and provenance

The following source text was accessed directly in this pass; none is used as evidence of novelty for this report's elementary lemma.

- **Peter Stevenhagen, “The number field sieve,” Section 3, printed page 87 (PDF page 5).** Explicitly discusses computing norms of higher-degree polynomial expressions by resultants. Higher-degree sieving elements and the resultant identity are therefore established background. Sections 4–10 explain why norm smoothness/ideal parity alone do not complete square extraction. [Primary PDF](https://pub.math.leidenuniv.nl/~stevenhagenp/ANTproc/04psh.pdf).
- **Shi Bai, Richard P. Brent, Emmanuel Thomé, “Root optimization of polynomials in the number field sieve,” Sections 2–5, especially PDF pages 5–6 and 9–11.** Separates size optimization from improving modular root properties of the defining polynomial, using rotations and sieving. This is not evidence that archimedean evaluation slabs for the sieving element have many integer points. [Primary preprint](https://arxiv.org/pdf/1212.1958v1).
- **Don Coppersmith, “Modifications to the Number Field Sieve,” 1993**, primary publication record, and **Jonathan Lee–Ramarathnam Venkatesan, “Rigorous Analysis of a Randomised Number Field Sieve,” Remark 4.31** for the exact multiple-polynomial comparison constant. The checked remark concerns square congruences; it is not cited as unconditional general factor extraction. [Coppersmith record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve), [Lee–Venkatesan text](https://arxiv.org/html/1805.08873v1).
- **Michael Sagraloff–Kurt Mehlhorn, “Computing Real Roots of Real Polynomials,” Theorems 2–3.** Supplies certified real-root isolation/refinement with polynomial bit complexity for integer polynomials and requested precision. Only this complexity fact is used, not an unverified numerical root routine. [Primary preprint, v2](https://arxiv.org/pdf/1308.4088v2).

`H008-resultant-provenance.json` records SHA-256 hashes of the consulted local inputs and this final report, the source URLs, and the explicit no-experiment disposition. A hash binds a document version; it is not independent mathematical validation. No source-code or run-result hash is fabricated when no experiment exists.

## 8. Handoff and evidence level

**Best supported result:** the elementary resultant bound (5) and its at-most-d corollary rigorously reject this precise thin-window, primitive-irreducible-quadratic relation-population proposal, subject to independent checking of the written proof. The reference enumerator is fully specified with charged \(H^3\operatorname{poly}(n)\) work, but was not implemented or run. Its norm bound is deterministic; its originally hoped-for factoring constant remains an unattained conditional heuristic.

**Next decisive action:** independent review of the column-operation resultant proof, reversal step, the numerical factor 72, and the correspondence between the irreducibility filter and Card C's intended candidate set. If those survive review, archive this selector as rejected and require any replacement to state which hypothesis of the lemma it changes. A finite scan is unnecessary to establish this rejection and cannot establish a general escape.

No new general classical factoring complexity, smaller heuristic L constant, smaller L exponent, or polynomial-time algorithm has been established. Verified improvement remains **NONE**.
