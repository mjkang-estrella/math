# Independent preliminary review: full shifted Jacobi denominator law

Reviewer: Sol, solo, no children. Reviewed frozen commit `9cf59803fe`, using independently copied bytes. Review began 2026-10-28 UTC and concluded 2026-10-29 UTC (October 28 in America/Los_Angeles). This is an investment recommendation, not an acceptance or count instruction.

**Recommendation: INVEST in the literal formalization.** The complete ordinary proof in the union of r3 `discovery.md` and r4 `PROOF.md` survives this independent adversarial review. I found no mathematical counterexample or missing ordinary bridge. The substantive contribution is the all-coefficient midpoint arithmetic bound, together with a proved literal source bridge; the top coefficient alone would not qualify. Acceptance remains **HOLD**, principally because the literal Lean endpoint and paper are absent.

| Gate | Decision | Exact scope |
|---|---|---|
| SOURCE | **PASS** | Literal formal Definition 2.1, (6)-(7), and shifted Remark 3.8 of current primary v2. No analytic identification asserted. |
| MATH: source bridge | **PASS** | Independent all-order derivation of the ODE, Riccati identity, degree, parity, constants and top attainment. |
| MATH: all-coefficient arithmetic | **PASS** | Independent derivation of both pairings, coefficient parity, integral normal form, odd-unit inversion and exact degree scaling. |
| NOVELTY | **PASS, bounded** | No same-object public shifted-law resolution or complete subsumer located in the live sources/registries and targeted literature below. No global priority certification. |
| SUBSTANTIVE | **PASS for investment** | A distinct full source question is answered by the filtered midpoint argument. No immediate published classical-specialization bridge was found; strongest routine objection remains documented below. |
| FORMAL | **HOLD** | Five tiny arithmetic helpers replay successfully. No literal source theorem, no full arithmetic filtration, no attainment theorem. |
| PAPER | **HOLD** | No candidate manuscript/paper supplied in the frozen full candidate. |
| FULL EXTRACTED STRICT REPLAY | **HOLD** | No complete literal certificate/packet exists to replay. Tiny-helper replay is not this gate. |
| FREEZE | **PASS** | 21/21 expected, frozen-commit, independently copied and working-file hashes match before and after. Manifest checked separately. |
| COUNT / ACCEPTANCE | **HOLD; no credit** | Candidate remains 0; total remains 32/60. Reviewer made no ledger or candidate changes. |

## 1. Evidence, exact object and publication status

The actual source bodies were read, including primary Definition 2.1, Theorem 2.3, Section 3's valuation proof, Computational observation 3.1, Corollary 3.7 and Remark 3.8; and companion definitions, Theorems 1.5/1.6/7.36, Proposition 7.37, the layer and transverse constructions, Section 10's valuation statements and Section 11. Fresh public HTTP retrievals of both v2 bodies are byte-identical to the frozen raw sources. Fresh abstracts and a live author search establish the current versions, rather than relying on cached registry prose or search-engine titles.

The primary is [Area, arXiv:2608.23006v2](https://arxiv.org/html/2608.23006v2). Its actual definition is

\[
 F=\sum_{s\ge0}C_s e_s(Z),\quad e_s(Z)=\prod_{j=1}^s(Z-j)^{-1},\qquad
 \kappa_r=2^{-(2r-1)}\operatorname{Im}[Z^{-(2r-1)}]\log F\big|_{x=(1+i)/2,y=(1-i)/2}.
\]

The Hankel product becomes \(a_\ell(\alpha)=P_\ell(u)/(2^\ell\ell!)\), where \(P_\ell(u)=\prod_{j<\ell}(u-j(j+1))\), so
\(C_s=\sum_{\ell=0}^s P_\ell(u)P_{s-\ell}(v)x^\ell y^{s-\ell}/(\ell!(s-\ell)!)\).
This is a polynomial identity in independent \(u,v\); it does not require admissible analytic parameters or an analytic phase expansion.

For every integer \(r\ge1\), the reviewed claim is precisely
\[
 \max_{\text{nonzero coefficients }c\text{ of }\kappa_r(u,v)}\max(0,-\nu_2(c))
 =2r+\nu_2((r-1)!).
\]
This is the exponent in the common rational denominator. It is not an assertion that the entire denominator is a power of two, nor an original-variable denominator assertion. Zero coefficients cause no issue.

Primary v1: **2026-08-24 09:10:08 UTC**; current v2: **2026-10-05 05:40:44 UTC**. Companion [arXiv:2609.29531v2](https://arxiv.org/html/2609.29531v2): v1 **2026-08-25 09:34:51 UTC**, current v2 **2026-10-14 14:02:16 UTC**. These are the actual submission-history dates, including the companion's August v1 date despite its September identifier. Neither current abstract page supplies a journal reference or a journal DOI; the DOI link shown is the arXiv-issued DataCite DOI. These are publicly available preprints. I do not invent a journal/VoR prerequisite or hold the source gate for an unidentified publication.

The primary explicitly leaves the shifted denominator open. Its top-coefficient identity was computational, not an all-order theorem. Its interpretation as analytic phase constants beyond the checked range remains conditional. The candidate's new algebra proves the needed *formal* bridge and the top identity; it does not close the broader analytic identification question. That distinction must remain in a future paper and theorem wrapper.

The companion proves the valuation of the original \([A^1B^0]\kappa_r\) / Legendre tangent, with exponent \(3r-1+\nu_2((r-1)!)\). Its Section 10 auxiliary valuations concern numerator/denominator series at the Legendre point; Section 11 retains the larger shifted upper bound. Its diagonal and first-transverse results do not bound every shifted mixed coefficient. The original-variable law is excluded from discovery credit here.

The actual [MathDB 391922 rendered statement](https://mathdb.com/p/391922/dyadic-denominator-law-for-the-phase-constants-of-the-jacobi) was independently read using public web retrieval: it is in \(A,B\), with exponent \(3r-1+\nu_2((r-1)!)\), and its progress prose says the companion was not retrieved. It is a stale original-law open record, not evidence that the shifted problem is open. No solution-list absence is used as novelty evidence. A subsequent direct HTTP attempt on the public rendered URL returned 403; I stopped requests there. I did not access its API or bypass the denial.

## 2. Independent source-to-Riccati derivation

I checked the actual source normalization, rather than assuming agreement with a WKB sequence. Use \(\xi=(1+it)/2\), \(\eta=(1-i/t)/2\) to distinguish the source coordinates from the later midpoint coordinate \(x\). Then \(2\xi\eta=\xi+\eta\), and
\[
 D=-(1+t^2)\frac d{dt}=2i\delta,\qquad
 \delta=\xi(\xi-1)\partial_\xi+\eta(\eta-1)\partial_\eta.
\]
Indeed \(D\xi=-i(1+t^2)/2=2i\xi(\xi-1)\), and the analogous identity holds for \(\eta\). Let \(Q=\xi^2\partial_\xi+\eta^2\partial_\eta\), \(\Theta_\xi=\xi\partial_\xi\), and similarly for \(\eta\).

From \(P_{\ell+1}(u)=(u-\ell(\ell+1))P_\ell(u)\), coefficient comparison gives
\[
 \partial_\xi C_{s+1}=(u-\Theta_\xi(\Theta_\xi+1))C_s,
\]
with the corresponding \(v,\eta\) equation. On an arbitrary test polynomial, expanding the two differential operators gives
\[
 \delta Q=\xi(\xi-1)\Theta_\xi(\Theta_\xi+1)
 +\eta(\eta-1)\Theta_\eta(\Theta_\eta+1)
 +\xi\eta(2\xi\eta-\xi-\eta)\partial_\xi\partial_\eta.
\]
The mixed term vanishes on the curve. Consequently
\[
 \delta(C_{s+1}+QC_s)=(u\xi(\xi-1)+v\eta(\eta-1))C_s=-VC_s/4,
 \quad V=u(1+t^2)+v(1+t^{-2}).
\]
Homogeneity supplies \(QC_s=(\delta+s)C_s\), so
\[
 D^2C_s+2isDC_s+2iDC_{s+1}-VC_s=0.
\]
Using \(Ze_s=e_{s-1}+se_s\) for \(s\ge1\), including \(DC_0=0\), summation yields exactly
\[
 D^2F+2iZDF-VF=0.
\]
This is legitimate in the formal \(Z^{-1}\)-adic ring: a coefficient at fixed order uses only finitely many \(s\). There is no analytic convergence or branch assumption.

Since \(F\) has constant term 1, \(q=DF/F=D\log F\) is defined and satisfies \(Dq+q^2+2iZq-V=0\). Equating coefficients in powers of \((2iZ)^{-1}\) gives uniquely
\[
 q=\sum_{n\ge1}\frac{s_n}{(2iZ)^n},\qquad
 s_1=V,\quad s_{n+1}=-Ds_n-\sum_{i+j=n\atop i,j\ge1}s_i s_j.
\]
The sign of \(2i\) and the source's additional factor \(2^{-(2r-1)}\) are both necessary.

Induction proves integral Laurent coefficients, membership in \((1+t^2)\), \(t\)-parity \((-1)^{n+1}\), no parameter-constant term, and degree at most \(\lceil n/2\rceil\). For the product bound, at even \(n=2m\), odd/odd indices give degree at most \(m+1\), even/even at most \(m\); at odd \(n=2m+1\), the odd/even case gives at most \(m+1\). These are exactly the induction bounds for \(s_{n+1}\).

The source \(L_n(t)\) is a Gaussian-rational Laurent polynomial and satisfies \(L_n(-t)=\overline{L_n(t)}\). Its imaginary part is therefore odd in \(t\). For even \(n\), \(DL_n=s_n/(2i)^n\) is real, so the imaginary part has derivative zero. The kernel of \(D\) on Laurent polynomials in characteristic zero consists of constants: cancel the nonzero factor \(1+t^2\) and compare derivative coefficients. An odd constant is zero. This repairs the earlier invalid inference of reality from swap symmetry.

For odd \(n=2r-1\), \(s_n/(1+t^2)\) is even Laurent. Integrating its monomials divides only by nonzero odd integers, hence defines an odd Laurent \(D\)-primitive \(J_t(s_n)\). Kernel uniqueness and source imaginary oddness give
\[
 \operatorname{Im}L_{2r-1}(t)=\frac{(-1)^r}{2^{2r-1}}J_t(s_{2r-1}),
 \qquad \kappa_r=\frac{(-1)^r}{2^{4r-2}}J_t(s_{2r-1})(1).                 \tag{S}
\]
No integration constant remains. This does not rely on midpoint conjugation alone.

For the claimed degree bound on the entire \(L_n\), any excess parameter coefficient has zero \(D\)-derivative and is constant in \(t\). At \(t=i\), both source coordinates are zero, so \(F=1\) and all \(L_n=0\). That constant is zero. Evaluation is valid in the Gaussian-rational Laurent ring because \(i\ne0\).

At spectral index \(2r-1\), only odd/odd products contribute to parameter degree \(r\). Writing the top coefficient as a scalar times \(V^r\), its recursion is the Catalan recursion with alternating sign. Thus
\[
 [\deg r]s_{2r-1}=(-1)^{r-1}\operatorname{Cat}_{r-1}V^r.
\]
The pure \(u^r\) odd primitive of \((1+t^2)^r\) is
\(-\sum_{j<r}\binom{r-1}{j}t^{2j+1}/(2j+1)\). Combining signs with (S) gives the positive, nonzero coefficient
\[
 [u^r]\kappa_r=\frac{\operatorname{Cat}_{r-1}}{2^{4r-2}}
 \sum_{j<r}\binom{r-1}{j}\frac1{2j+1}.                              \tag{T}
\]
This independently proves the previously computational top formula for every \(r\); the \(v^r\) coefficient has the opposite sign by actual source antisymmetry. Hence the degree is exactly \(r\).

## 3. Independent arithmetic derivation, including the vulnerable steps

Work in \(R=\mathbb Z[x,w]/(w^2-x^2-1)\). Division by the monic quadratic in \(w\) gives the unique integral normal form \(A(x)+wB(x)\). Thus \(R\) is torsion-free over \(\mathbb Z\). Over \(\mathbb Q\), the maps
\[
 x\mapsto(t-t^{-1})/2,\quad w\mapsto(t+t^{-1})/2,
 \qquad t\leftrightarrow w+x,\quad t^{-1}\leftrightarrow w-x
\]
are inverse isomorphisms. Torsion-freeness proves the integral ring's injection into the rational Laurent ring. There is no integral inverse-coordinate assertion.

The derivation \(\partial x=-(1+x^2)\), \(\partial w=-wx\) annihilates the defining relation and preserves \((w)\): \(\partial(wf)=w(-xf+\partial f)\). In these coordinates \(D=2\partial\). Set \(a=u+v,b=u-v\), \(P=a(1+x^2)+bwx\). Direct expansion gives \(V=2P\).

Let \(h_1=P\), \(h_{n+1}=-\partial h_n-\sum_{i+j=n}h_i h_j\). Degree \(d\) transforms as
\[
 [\deg d]s_n=2^{n+1-d}[\deg d]h_n.                                 \tag{A}
\]
For the derivative, applying \(D=2\partial\) adds one factor 2. For a product of degrees \(e,f\), \((i+1-e)+(j+1-f)=n+2-d\), exactly the exponent at \(n+1\). All terms have positive parameter degree and \(d\le\lceil n/2\rceil\), so no negative power of 2 is hidden here.

There are genuinely two different symmetry operations. \(\rho(x)=x,\rho(w)=-w\) commutes with \(\partial\), and \(\rho P(a,b)=P(a,-b)\). Uniqueness/induction gives \(\rho h_n(a,b)=h_n(a,-b)\). Since the ring is torsion-free, the \(a^ib^j\) coefficient has even \(w\)-normal component only for even \(j\), and odd \(w\)-normal component only for odd \(j\). In contrast, \(\tau(x,w)=(-x,-w)\) anticommutes with \(\partial\) and gives \(\tau h_n=(-1)^{n+1}h_n\). It controls combined \(x,w\) parity, not \(b\)-coefficient parity by itself.

All \(h_n\) belong to \((w)\), separately at each parameter coefficient. A normal form belongs to \((w)\) exactly when its even component is divisible by \(1+x^2\): expand \(w(C+wD)=(1+x^2)D+wC\). Therefore, at odd \(n\), every homogeneous piece has the *integral* form
\[
 H=(1+x^2)A(x^2)+wxB(x^2).                                       \tag{B}
\]
Monic division preserves integrality; combined parity makes the quotients polynomials in \(x^2\). This includes mixed parameter coefficients.

For a nonconstant bidegree \(\alpha=(i,j)\), let \(q(\alpha)=s_2(i)+s_2(j)-1\ge0\). Binary subadditivity and doubling yield
\[
 q(\alpha+\beta)\le q(\alpha)+q(\beta)+1,\qquad q(2\alpha)=q(\alpha).
\]
In the additive class \(\mathcal C\) of no-constant parameter polynomials whose coefficient at \(\alpha\) lies in \(2^{q(\alpha)}R\), these facts prove closure under **\(2fg\)** and under **\(f^2\)**. They do not prove closure under \(fg\).

For a square, expand by unordered pairs of parameter monomials: distinct monomials contribute \(2f_\alpha f_\beta\); diagonal monomials contribute \(f_\alpha^2\), with valuation at least \(2q(\alpha)\ge q(2\alpha)\). This is the first necessary quadratic pairing. Independently, in the recurrence's spectral convolution, unequal indices \(i,j\) occur twice and give \(2h_i h_j\); at an even convolution index the remaining term is a square \(h_{n/2}^2\). This is the second necessary pairing. Strong induction from \(P\in\mathcal C\), plus preservation by \(\partial\), gives \(h_n\in\mathcal C\) at every order. Treating the convolution as arbitrary products would be a real gap; the current proof does not do that.

If \(j\) is odd and \(i+j=d\),
\[
 q(i,j)=s_2(i)+s_2(j-1)\ge s_2(d-1).
\]
Together with the \(\rho\) coefficient rule, this makes every coefficient of \(B\) in (B) divisible by \(2^{s_2(d-1)}\). The even component does not need that bound.

Localize only the scalar integers at 2. The even component of (B) has primitive
\(-\sum_k A_kx^{2k+1}/(2k+1)\), with odd denominators and midpoint value zero. For the odd component,
\[
 \partial(wf(x^2))=-wx\{f(x^2)+2(1+x^2)f'(x^2)\}.
\]
On polynomials of degree at most \(N\), \(Tf=f+2(1+X)f'\) is triangular with diagonal \(2k+1\) and lower neighbor coefficient \(2(k+1)\). It is invertible over \(\mathbb Z_{(2)}\), using downward recursion
\[
 f_k=(-B_k-2(k+1)f_{k+1})/(2k+1),\quad f_{N+1}=0.
\]
Only odd units are inverted. Every fixed factor \(2^e\) in \(B\) survives in all \(f_k\); an ordinary rational-polynomial inverse alone would not have been enough, but this explicit inverse proves the required preservation.

The constructed primitive is \(\tau\)-odd, hence becomes odd under \(t\mapsto-t\). The Laurent-kernel argument in Section 2 identifies it with the unique normalized primitive in (S). At \(t=1\), \(x=0,w=1\). Dividing (A) by the factor 2 in \(D=2\partial\) leaves
\[
 [\deg d]J_t(s_n)(1)\in 2^{n-d+s_2(d-1)}\mathbb Z_{(2)}[a,b].        \tag{C}
\]
The direction \(a=u+v,b=u-v\) is an integral polynomial substitution, so it preserves (C). No inference of integrality uses the inverse substitution with halves.

For \(n=2r-1\), Legendre's identity gives
\[
 n-d+s_2(d-1)=2r-2-\nu_2((d-1)!).
\]
Multiplying each homogeneous piece by \((d-1)!\) therefore puts it in \(2^{2r-2}\mathbb Z_{(2)}[u,v]\). Since \((d-1)!\mid(r-1)!\) for \(1\le d\le r\), summing all pieces proves
\[
 (r-1)!\,J_t(s_{2r-1})(1)\in2^{2r-2}\mathbb Z_{(2)}[u,v].          \tag{G}
\]
Using (S), all coefficients of \(\kappa_r\) have valuation at least \(-2r-\nu_2((r-1)!)\). This is the full missing upper bound, including all mixed and lower-degree terms. Odd rational denominators are allowed throughout and do not change the dyadic exponent.

At \(r=1\), the midpoint primitive of \(P\) is \(-ax-bw\), with value \(-b\). Thus \(J_t(s_1)(1)=-(u-v)\), \(\kappa_1=(u-v)/4\), and \(\delta_1=2\). The zero-degree exclusion, \(s_2(0)=0\), and \(0!=1\) all agree. There is no exceptional initial-order gap.

For exactness, the public primary Theorem 1.4 gives \(\nu_2(I_r)=r-1+\nu_2(r)\). Since \(\nu_2(\operatorname{Cat}_{r-1})=s_2(r-1)-\nu_2(r)\), (T) has valuation
\(s_2(r-1)+r-1-(4r-2)=-2r-\nu_2((r-1)!)\). The pure \(u^r\) witness attains (G)'s uniform bound. No cancellation between different parameter monomials is being assumed.

## 4. The primary binomial theorem is a real formal obligation

I read the primary's proof, not just its theorem label. Put \(c_k=k!/(2k+1)!!\), with \(\nu_2(c_k)=\nu_2(k!)\to\infty\), and \(M_i=\sum_{k\ge i}c_k\binom{k}{i}\). The convergence bound is \(\nu_2(M_i)\ge\nu_2(i!)\). For \(i\ge1\), the recurrence for \(c_k\), with the zero boundary binomial at \(k=0\), gives \((i+1)M_{i+1}=iM_{i-1}\). Thus \(M_{2j}=M_0\binom{2j}{j}/4^j\). Its direct lower bound and this identity force \(M_0=0\).

The finite binomial transform is \(I_{m+1}/2^m=\sum_{k=0}^m(-1)^k\binom{m}{k}c_k\). For tails \(R_j=\sum_{k\ge j}c_k\), summation by parts writes this as
\(R_0+(m+1)\sum_{j=1}^{m+1}(-1)^j\binom{m}{j-1}R_j/j\).
Now \(R_0=0\), \(R_1=-1\), \(R_2=-4/3\); all \(R_j/j\) for \(j\ge2\) are even 2-adic integers. The remaining sum is a unit, proving the stated valuation. This establishes the ordinary dependency's content. For the needed forward implication, there is no need to formalize the source's converse Mahler-continuity argument.

I inspected actual pinned mathlib blobs at `d13f23b723b8a846827a245b89c10fc7d3f11612`, copied under `library/`, and verified their working bytes match. `PadicVal/Basic.lean` has `sub_one_mul_padicValNat_factorial` with type
`(p - 1) * padicValNat p (n !) = n - (p.digits n).sum`, and `sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` with type
`(p - 1) * padicValNat p (choose (n + k) k) = (p.digits k).sum + (p.digits n).sum - (p.digits (n + k)).sum`, under `Fact p.Prime`.
These supply Legendre/Kummer arithmetic, not the reciprocal-odd-denominator binomial-sum theorem. Targeted searches in the pinned padics, digit and binomial-sum sources found no literally equivalent existing theorem. This is a bounded library inventory, not a proof that none exists elsewhere in mathlib.

## 5. Own falsification diagnostics and former failure modes

`own_checks.py` imports no candidate code and no SymPy. Its structure differs from the candidate and root checkers: it first constructs universal differential polynomials in jets, evaluates them in the two coordinate systems, expands the literal source logarithm by direct powers of `F-1`, integrates by exact Laurent long division, and transforms that primitive back to midpoint coordinates by binomial expansion. It does not implement a pair-ring recurrence plus simultaneous primitive linear solve, nor the scaled cumulant checker.

The finite run passed. Normalized jet/filtration/scaling/ideal/parity/primitive checks cover `n<=11`; literal source logarithm and derivative comparison cover `n<=7`; exact binomial valuations cover `m<=64`; odd-unit inverse preservation is checked on bases through polynomial degree 12. Mixed coefficients are present from `r=3` and are checked coefficientwise, not by specialization to pure parameter lines. The script's inverse half-substitution is used only to compare exact identities, never to justify an integrality deduction.

The exact negative controls retain the strongest simple falsifiers:

- The primitive's pure \(u^2\) coefficient at \(r=2\) is \(t+t^3/3\): its separate Laurent coefficients fail divisibility by 4, whereas the midpoint value \(4/3\) has valuation 2. A proof transferring (G) to every Laurent coefficient would fail.
- The arbitrary shifted-moment extension fails at \(\sum_{j=0}^3\binom3j/(2j+3)=464/315\), valuation 4 rather than 5.
- The weighted class is not a subring: \(a,b\in\mathcal C\), but \(ab\notin\mathcal C\). The two explicit pairings, rather than generic multiplication, are essential.
- A constant added to a primitive survives differentiation but violates the source's odd normalization. The current proof uses the kernel plus oddness to exclude exactly that possibility.

The current proof repairs the earlier parity, equivalence and missing-degree claims by actual arguments. I have not certified the old checker or inherited any previous PASS. The direct finite log comparison would catch an incorrect normalization even when a Riccati recurrence self-check passes. Finite diagnostics only falsify possible errors; the unbounded conclusion follows from Sections 2-4, not from the tested ranges.

`own-checks.json` records an observed high-water RSS of **505820 KiB**, below 512 MiB (524288 KiB), with a hard 500 MiB virtual-address cap for that Python process. The unusually high reported high-water number is retained as reported, not replaced by an estimate. No broad mathlib import was run.

## 6. Live bounded novelty, exact chronology and substantive objection

Fresh HTTP evidence is in `evidence/`, with URLs, UTC retrieval times, status and SHA-256 receipts. The initial live source/registry retrievals occurred at **2026-10-28 23:56:52-23:56:56 UTC**.

- `openai/math`: observed live HEAD **7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a**, commit **2026-10-26 21:18:03 UTC**. Separate `preprints` subtree **3f56f68a176b4494c346091ea0a319651bc217ec**, **13578 entries, truncated=false**, and the actual current `CONTENTS.md` were downloaded. This is not the old October 8 accepted-theorem pin.
- `the-omega-institute/trureturing`: observed live HEAD **e315a2581568bc01e825839649360fa5702f07df**, commit **2026-10-28 23:44:44 UTC**. This is newer than both r3's `40d003...` and r4's `e1b5b0...`. Separate `Problems` (**1527**), `D5` (**12409**) and `Blueprint` (**22954**) trees each report **truncated=false**. Their actual bytes are unchanged relative to the r4 subtree receipts despite the newer repository HEAD. Current README was fetched too.

The screens cover Jacobi, ultraspherical, phase constants, the source IDs, denominator, dyadic, Riccati, Gel'fand-Dikii/KdV, plus catalogue context. Full hit lists are retained. No exact same-object result was identified. OpenAI's denominator matches are geometry/dynamics or unrelated arithmetic; Omega's Jacobi matches concern matrices/moments, vertex algebras, Weil constructions and metallic Hankel recurrences. This is a path/catalogue selection screen, not blanket reading of every theorem in either registry.

I independently fetched and read the entire actual Omega `CompositionalSquareDyadicDenominators` Blueprint and problem body at the current immutable head, plus the Lean source (its initial definitions/proof structure and target statements were inspected). It concerns \(X(A+1)=A\circ A\), normalized at constant coefficient zero and linear coefficient one, with an integral rescaling and triangular composition residual. It supplies neither the source bridge nor the multigraded Riccati/odd-primitive theorem. The similar denominator vocabulary is not a subsumption bridge. Exact immutable URLs and hashes are in `body-retrieval.json`.

Current author search at **2026-10-29 00:00:37 UTC** returned **29/29** `Area, Ivan` results on one page. The latest other paper, `2610.23031` (October 16), concerns Stieltjes moment functionals; the two actual phase-constant papers are the current v2 primary and companion already read. Their source chronology predates this candidate's October 28 proof. No additional matching author followup was identified. The unrelated Stieltjes work was screened by its actual search-result abstract; I do not claim to have read its full manuscript.

Public web queries included the exact primary/companion identifiers with shifted/proof, Jacobi phase shifted denominator, Area's author name with denominator/October 2026, Riccati with binary divisibility/2-adic/dyadic integrality, and Gel'fand-Dikii denominators/integrality. Search hits often retain the primary v1 title and old abstract. I used the fresh actual v2 bodies to decide scope. No matching shifted-law proof was found. Web search results have no local immutable raw-response byte hash; the search log is a review record only.

For a concrete classical-method challenge, I fetched the actual Kauers-Krattenthaler-Müller paper, *A method for determining the mod-2^k behaviour of recursive sequences, with applications to subgroup counting*, EJC **18(2) (2012), P37**, from the public EMIS journal mirror. Its Section 4 (actual pp.16-20), Remark 11, Lemma 12 and Catalan Theorem 13 were inspected. The method assumes an integral power-series solution and seeks a representation modulo a fixed power of 2 in a binary lacunary series, solving successive systems which need not be solvable. That is not a ready theorem giving this bidegree weight, midpoint primitive or sharp denominator at all spectral orders. No literal specialization was established. I do not claim its techniques could never yield another proof.

**Strongest substantive objection:** the filtration closure is an elementary binary-digit argument for a quadratic recurrence, and the primitive is elementary triangular inversion. A sufficiently general previously published theorem about these exact weighted differential recurrences and midpoint functionals could turn the result into a routine corollary. Classical WKB/Riccati integrality alone is weaker: it does not provide the missing \(s_2(d-1)\) gain after selecting the odd component and evaluating its normalized primitive. The explicit \(r=2\) Laurent falsifier shows why integrality alone is insufficient. I found no published theorem whose hypotheses can simply be substituted to deliver all of (S), (C) and (G). Thus the full filtered assembly qualifies for investment; the classical ingredients and top-only result receive no separate credit.

The known original-variable theorem, the source valuation theorem, and the first campaign's already published thirty outcomes are not counted anew. No matching later independent public counterpart was found. A current registry HEAD's date is not itself the publication date of every body; I do **not** classify an unlocated counterpart as earlier just because a current HEAD precedes this review. If one is found, its actual content and first relevant commit/publication time must be compared with the candidate's proof provenance. This bounded screen gives no worldwide-priority guarantee, full citation-network audit, subscription-index search, or proof of absence under unexpected titles.

Access limits: the author-hosted KKM PDF failed certificate verification; I did not disable TLS verification. The public EMIS mirror returned 200 and supplied the complete paper. Web retrieval of the old arXiv HTML and later EMIS `find` requests timed out; no conclusion was inferred from those failures. The MathDB rendered direct request returned 403 and was not retried or bypassed. All these failures are retained. No 429 was encountered.

## 7. Formal inventory and recommended decomposition

The actual frozen Lean file defines only `Dyadic : Nat -> Nat -> Prop` and proves:
`dyadic_mul`, `dyadic_doubled_product`, `dyadic_weaken`, `dyadic_square`, and `dyadic_doubled_product_weaken`. These are scalar natural-number divisibility statements, with no source coefficients or Jacobi objects in their types.

A fresh replay from my frozen copy succeeded with the supplied Lean 4.34.1 executable, `-j1 -M256`, selective `prelude` imports, and no output `.olean` requested. All five actual axiom reports are `[propext]`. `own-lean-attempt3-receipt.json` records exit 0 and observed RSS **173940 KiB**, guarded at 450 MiB. Two bounded earlier attempts are preserved: a 4 GiB virtual-address limit prevented thread creation; a 16 GiB virtual limit with Lean's `-M128` reached the kernel memory guard. The latter's self-axiom error reports are failed elaborations and are not valid certificates. The successful third attempt used 16 GiB *virtual* allowance, not resident memory. Neither failure was suppressed or misreported as PASS.

**No full FORMAL PASS follows.** The candidate lacks definitions and closed proofs for the literal finite source coefficients; formal logarithm and ODE/Riccati equality; oddness and kernel normalization; the integral quadratic algebra and embedding; binary-weight coefficient filtration with both pairings; odd-unit primitive preservation; Catalan/top attainment; primary Theorem 1.4; and final exact-denominator assembly. A fresh complete extracted replay and paper are also absent.

The proposed wrapper in `LEAN-BRIDGE-PLAN.md` is faithful: define `sourceKappa r : MvPolynomial (Fin 2) Q` from finite coefficient extraction of (6) and its logarithm, take Gaussian-rational imaginary parts at the literal midpoint, and divide by \(2^{2r-1}\). The endpoint should assert all coefficients become 2-local at exponent \(2r+\nu_2((r-1)!)\), while the coefficient at the pure-u monomial fails to be 2-local one exponent lower. This is exactly the source's dyadic denominator claim, provided every source-to-recurrence bridge is proved internally and not supplied as a premise. The exponent is at least 2, so its predecessor is safe even at \(r=1\).

Recommended order of investment:

1. **Define the literal source object first**, using finite coefficient lists and rational Gaussian pairs if that keeps imports small. Fix the Hankel product, empty inverse-factorial product, log truncation, imaginary projection and source midpoint in one auditable module.
2. **Prove the source ODE and normalized Riccati bridge**, including imaginary oddness and the zero Laurent derivative kernel. Do not replace this with an axiom or analytic-phase assumption.
3. **Build the midpoint ring as polynomial pairs**, with explicit multiplication and derivation. Prove normal-form uniqueness, integral `(w)` membership, rho/tau separately and exact degree scaling. This may avoid quotient-ring automation overhead.
4. **Prove the weighted-class theorem abstractly** over a commutative integer algebra with a parameter-preserving derivation. Keep the square's parameter-monomial pairing distinct from the recurrence's spectral-index pairing. The five helpers are only a small scalar portion of this module.
5. **Prove the finite triangular primitive lemma** over a 2-local rational subring; transfer divisibility only in the integral direction \(a=u+v,b=u-v\). Then prove (G) using pinned Legendre types.
6. **Develop attainment as its own substantial module**: Catalan top degree plus the reciprocal-odd-denominator binomial valuation. The source's moment proof gives a precise route; its Mahler converse can be omitted. Do not mistake generic Kummer or factorial valuation lemmas for a proof of this finite sum.
7. **Assemble the premise-free literal endpoint**, audit actual types/axioms and forbidden constructs, then write/review the paper and perform the required fresh extracted strict replay. Only root may subsequently decide acceptance/counting.

The ordinary proof warrants this work, with formal effort expected to be substantial. The strongest remaining concrete risk is underestimating the literal source and binomial-valuation formalization, not an identified defect in the ordinary filtered-ring argument.

## 8. Freeze and scope accounting

`freeze-before.json` and `freeze-after.json` contain all 21 manifest paths with expected SHA-256, frozen commit bytes, my independent byte-copy hash and working-file hash. All agree. The manifest itself is also checked against the frozen commit and its before/after copy. `provenance.json` indexes the results and evidence hashes.

All writes made by this review are under this assigned review lane. No candidate edits, shared/root/other-lane edits, ledger/count changes, staging or commits occurred. Git was used only for read-only `show` of frozen input and pinned library blobs. No Karp/BBK active worker contents were read or polled. No children, external messages/posts/uploads, account mutations, preview/browser tabs or access-control bypass were used. The only network actions were bounded public read-only HTTP/search.
