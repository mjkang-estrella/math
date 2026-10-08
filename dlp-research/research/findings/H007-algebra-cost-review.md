# H007 independent algebra cost/prior-art review (T3 Astra)

Paper review, no experiments or Lean claims. Root synthesis controls accepted scope; dictionary expansion and coverage arguments are separately identified below.

**Two hypotheses survive, but neither supports an improvement over the square-root baseline. Verified improvement remains NONE.** I rank the random-dictionary divisor selector first for further analysis, and GRR second, restricted to explicitly admissible factor bases.

I read the loop instructions and both proposals, inspected the relevant primary papers, and performed only paper analysis. No files were edited, numerical trials run, or children launched. GRR equation and exception correctness remain with the other reviewer.

Prior art substantially narrows the possible novelty:

- **Symmetric coordinates are established.** Joux–Vitse already solve using elementary symmetric functions, recover roots of the associated divisor polynomial, and test signs. Faugère–Huot–Joux–Renault–Vitse §3.3 explicitly discusses partially symmetrized target equations; its additional torsion symmetries and extension-field results do not automatically transfer to arbitrary prime-order prime-field curves. [Joux–Vitse](https://www-fourier.univ-grenoble-alpes.fr/~viva/research/articles/DLFq5.pdf), [EUROCRYPT 2014 paper](https://www.iacr.org/archive/eurocrypt2014/84410158/84410158.pdf).
- **Avoiding a factor-base linear-algebra stage is established.** Amadori–Pintore–Sala §3 builds random points with recorded \(uP+vQ\) representations, then seeks one signed zero-sum relation. It uses vanishing-polynomial membership, including partitioned dictionaries. The present known-log dictionary differs in keeping a reusable dictionary and shifting the target; “one relation suffices” is not new. APS explicitly leaves polynomial-system complexity unresolved. [APS, §§3–3.3](https://iris.unitn.it/retrieve/handle/11572/202653/186850/Amadori,%20Pintore,%20Sala%20-%20On%20DLP%20for%20prime-field%20EC%20(rev).pdf).
- **Low-degree membership chains are established.** PKM uses multiplicative-subgroup and auxiliary-isogeny chains, accounts for preprocessing, and leaves asymptotic solving complexity open. Its experiments decompose into two points; those timings do not establish GRR scaling. [PKM, §§3–5](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf).

The surviving distinction is therefore **a faster executable constrained-decomposition operation**, potentially exploiting the divisor representation—not symmetry, quadratic equations, or relation-count savings alone.

**First-ranked: random known-log dictionary, \(m=4\), with an unexpanded divisor-membership solver.**

Let \(S(B)\) include point generation, deduplication, construction of \(H\), and compilation. Let \(C(B)\) include every target-dependent operation, especially unsuccessful solves. With adequate coverage and reliable extraction,

\[
W_{\mathrm{dict}}
=\widetilde O\!\left(S(B)+\frac{q}{B^4}C(B)\right).
\]

For \(B=q^\beta\), \(S=q^{a+o(1)}\), and \(C=B^{\tau+o(1)}\), a strict exponent improvement requires

\[
a<\tfrac12,\qquad 1-(4-\tau)\beta<\tfrac12.
\]

At \(B=q^{1/5}\), this gives **\(\tau<3/2\)** and setup below \(q^{1/2}=B^{5/2}\). The stated \(C=o(B^{3/2})\) is the corresponding little-\(o\) work threshold; a strict exponent improvement needs a fixed exponent margin, with logarithmic factors accounted for.

There is a decisive **paper rejection of direct polynomial expansion at this parameter choice**. Write

\[
H(T)\bmod F(T)=r_0+r_1T+r_2T^2+r_3T^3.
\]

Assign weight \(i\) to \(e_i\). Since \(H\) is monic of degree \(B\), the highest-weight component of \(r_3\) is the complete homogeneous symmetric polynomial \(h_{B-3}\). Its expansion contains the monomials

\[
e_1^{a_1}e_2^{a_2}e_3^{a_3}e_4^{a_4},
\qquad a_1+2a_2+3a_3+4a_4=B-3.
\]

There are \(\Theta(B^3)\) such monomials. Their signed multinomial coefficients are nonzero when \(p>B\), and lower-degree terms of \(H\) cannot cancel this highest-weight component.

Thus **explicitly expanding even this one remainder coefficient costs \(\Omega(B^3)\)**, exceeding the \(B^{5/2}\) setup budget. This rejects that implementation at \(\beta=1/5\), not the underlying hypothesis. A fixed-\(m\), \(O(B)\)-size arithmetic DAG remains possible; efficient elimination from it is the missing operation.

The random-dictionary coverage concern also admits a useful paper argument. This is an independent derivation for review:

Take independent uniform \(a_i\in\mathbb F_q\). There are

\[
N=2^m\binom Bm
\]

signed, distinct-index coefficient vectors. For distinct vectors \(c,d\), their sums collide with probability \(1/q\), since \((c-d)\cdot a\) is a nonzero linear form for odd \(q\). If \(J\) counts colliding pairs and \(S\) is the set of represented group elements,

\[
\mathbb E J=\binom N2/q,\qquad |S|\ge N-J,
\]

so

\[
\Pr(|S|<N/2)\le (N-1)/q.
\]

Conditioning on nonzero scalars and distinct abscissae adds an \(O(B^2/q)\) rejection probability. Consequently, when \(B^m=o(q)\), most such dictionaries have \(\Theta(B^m)\) coverage. Independent uniform shifts then have success probability \(\Theta(B^m/q)\).

A restart after a fixed \(O(q/B^m)\)-trial block avoids relying on an uncontrolled average reciprocal coverage; rebuilding must be charged. This addresses **geometric coverage**, not whether a capped solver actually finds those representations.

The exact missing operation is:

> Given a paid representation of dense \(H\) and a target \(R\), find a valid degree-four divisor satisfying the summation constraint—or correctly finish an empty-target solve—in \(o(B^{3/2})\) work, without exceeding \(o(B^{5/2})\) compilation.

A conventional pair-sum search costs roughly \(B^2\) per target after building its table. At this parameter choice its complete search cost is roughly \(q/B^2=q^{3/5}\); it is a useful control, not the required selector.

An APS-style five-point zero-sum dictionary is another necessary control: at \(B\asymp q^{1/5}\), a constant-success attempt would permit total construction and solving below \(B^{5/2}\), but uses a different system and may rebuild the dictionary. Its solving cost cannot be identified with the four-point shifted-target cost.

**Second-ranked: GRR on an explicitly constructed structured base.**

Use the actual success probability \(s\), including chart restrictions, valid subgroup points, and extraction. For a collector taking at most one relation per successful target,

\[
W_{\mathrm{GRR}}
\approx S_{\mathrm{GRR}}
+\frac{r}{s}C_{\mathrm{GRR}}
+L(r,B),
\]

where \(r\) is the number of collected relations needed for a useful dependency. The usual estimates \(r=\Theta(B)\) and \(L=\widetilde O(B^2)\) require an appropriate sparse linear-algebra procedure and adequate relation quality.

Under the additional sparse-coverage assumption \(s=\Theta(B^m/q)\),

\[
W_{\mathrm{GRR}}
=\widetilde O\!\left(
S_{\mathrm{GRR}}+\frac{q}{B^{m-1}}C_{\mathrm{GRR}}+B^2
\right).
\]

For \(C_{\mathrm{GRR}}=B^{\tau+o(1)}\), the exponent conditions are

\[
\max\{a,\;1-(m-1-\tau)\beta,\;2\beta\}<\tfrac12.
\]

This corrects the proposed regimes:

- **Balanced \(m=5,\ B=q^{1/5}\):** require \(\tau<3/2\). The trial-count exponent matches the four-point known-log dictionary, but GRR also pays relation linear algebra. Its possible advantage is compact structured membership.
- **Balanced \(m=4,\ B=q^{1/4}\):** the stated \(B^2\) linear algebra already reaches square-root work.
- **Smaller-base \(m=4,\ B=q^{1/5}\):** still survives conditionally, requiring \(\tau<1/2\). With polylogarithmic target solves, the displayed accounting would give \(\widetilde O(q^{2/5})\).

Therefore, **“\(m\ge5\) is necessary” is only valid for the proposed balanced-base regime**, not for this whole mechanism.

The factorial argument needs repair. Counting unordered decompositions gives a **mean representation count** \(\lambda\), not a decomposition probability. Always,

\[
s\le\min(1,\lambda);
\]

a useful lower bound needs control of collisions or concentration. A Poisson heuristic would give \(s\approx1-e^{-\lambda}\). In particular, \(B^m\asymp m!q\) corresponds approximately to \(\lambda\asymp1\), not failure probability \(1-1/m!\). Removing permutation copies does not multiply the number of distinct target points covered.

The other reviewer’s chart and exception findings must feed into this coverage calculation. Counting ambient parameters or algebraic solutions cannot substitute for counting usable decompositions. The random-scalar collision argument above does not apply automatically to a structured abscissa set.

GRR setup is also paid: subgroup generation, usable-base identification, subgroup checks, chart construction, solver preprocessing, extraction, relation storage, and linear algebra all belong in the ledger.

The \(2^k\mid p-1\) version has restricted applicability. For secp256k1, the specified prime satisfies \(p\equiv3\pmod4\), hence \(v_2(p-1)=1\); no growing power-of-two subgroup is available. [SEC 2, §2.4.1](https://www.secg.org/sec2-v2.pdf).

PKM’s arbitrary-prime construction uses an auxiliary curve’s rational subgroup coset to define abscissae; it is not an isogeny transfer of the target ECDLP. A GRR adaptation still needs an explicit divisor-level rational-map recurrence, normalization and denominator handling, fiber coverage, and paid auxiliary construction. “Apply the chain to the divisor” does not yet supply that algorithm.

**The cheapest meaningful next screen is specification and symbolic cost analysis, before any pilot.**

1. For the dictionary candidate, require a concrete solver that retains the DAG or uses another representation avoiding the proved expansion cost. Specify compilation, target specialization, empty-system termination, and extraction. “Bounded sparse elimination” alone is insufficient.
2. For GRR, incorporate the independent correctness review, freeze one admissible family and chart policy, and give its effective coverage assumption and complete operation ledger. Compare the \(m=4\) sparse-base and \(m=5\) balanced regimes separately.
3. Only after authorization, use a small bounded pilot with unsuccessful targets explicitly represented and coverage-matched controls. The proposed \(m=2,\ldots,5\), \(k=2,\ldots,8\), 50-target grid has no demonstrated 60-second/1M-event fit.

A finite fitted slope can reject a frozen implementation over the tested range. It cannot prove an asymptotic exponent. Likewise, “degree rises once every two layers” is not a universal rejection criterion: actual matrix dimensions, fill, reductions, order conversion, and extraction determine paid work.

I would retain these two narrowly specified solver hypotheses, reject direct expanded-remainder F4 at the proposed dictionary parameters, and keep arbitrary-prime GRR conditional on its missing construction. No universal TT/sparse-support claim or broader losing-method theorem is needed for these conclusions.
