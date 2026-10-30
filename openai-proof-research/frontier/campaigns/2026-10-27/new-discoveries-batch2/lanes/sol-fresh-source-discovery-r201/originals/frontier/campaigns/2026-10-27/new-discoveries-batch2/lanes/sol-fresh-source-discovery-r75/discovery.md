# r75: full q-Fibonomial source question remains unresolved

Credit 0. No nomination, complete ordinary proof/refutation, PROOF.md, Lean, or paper. Counts remain 7 additional / 37 total; next 38. Root alone accepts outcomes.

## Selection and reconciliation

Read ancestor and batch AGENTS, current ledger, prior-campaign-context, NEXT, and r57–r73 summaries (also r74 to avoid its analysis topic). The broad follow-up match search found a material oversight: q-Fibonomial unimodality was investigated in the first campaign. Thus the initial description of this target as genuinely fresh was wrong. Initial searches of recent SUMMARY/discovery files did not include first-campaign FINDINGS files. The requested **all older matches before selection** gate was not met. This is a protocol deviation, not retrospective fresh-target clearance.

Actual older bodies subsequently reconciled:

* first campaign parent-qfibonomial/FINDINGS.md: full public Pacheco sufficiency and Patel necessity refutation for the different product conjecture; neither may be counted.
* parent-qfib-r14/FINDINGS.md: n=4 already follows from type-B2 Weyl principal specialization and principal sl2. Read actual cached Stembridge Theorem 7.4 proof, Corollary 7.5 and principal-sl2 explanation, printed pp31–32.
* pi-discrete-discovery-r2/FINDINGS.md: exact m,n<=12 tests and cyclotomic factorization already explored without a full result. Our finite confirmation is not new mathematics.
* prior-campaign-context exclusion 374707 explicitly leaves original 374706 open; this does not make it a fresh source.

The only reason for retaining a bounded revisit is a newly located public fourth-slice denumerant proof, plus transfer of that mechanism to arbitrary n and exact obstructions to several possible uniform closures. No claim that this mechanism is new to literature. No older unresolved source family is nominated. Sun A390107, numerical semigroups, Heim–Neuhauser, graph irregulators, and r74's Chernoff analysis were not pursued.

## Primary screens (three substantive questions, with an old lead immediately retired)

1. Gallardo et al.'s three-fold restricted-sumset conjecture, repeated as Goswami–Mistri 2603.04572v1 Conjecture 1.5: existence of an absolute c such that for every odd positive n and A subset Z/n, |A|>2n/5+c implies every residue is a sum of three distinct members. Actual source introduction read. **EXCLUDE PUBLIC**: Han–Ren 2610.14496v1 Proposition 3.1(a), entire pp7–8 proof read, proves for every odd-order finite abelian group N>=149 that |A|>2N/5 suffices. Choosing c=60 makes the condition vacuous for N<149 and covers the source fully. The proof uses representation counting, a translate of A-A, and Kneser. Lev's original author-hosted DVI is not read by the web tool (unsupported content type); the accessible independent full proof suffices for exclusion. No rediscovery credit.
2. Connelly et al. 2605.12822v1 Conjecture 5.4: all positive integer factors [a_i]_q times [b]_(q^r), divisibility-or-floor sufficient condition, and claimed necessity if k<=3 or r<=3. **EXCLUDE PUBLIC / OLD**. Actual pinned current Omega Library note, Blueprint explanation and actual Lean claim/result proof read. Its r=3,k=6,a_i=2,b=2 proof concerns necessity, not original Fibonomials. Older parent read Pacheco's full sufficient-direction proof. No residual variant pursued.
3. Bergeron–Ceballos–Küstner SIGMA16(2020)076 Conjecture 2.5, latest arXiv1911.12785v3 printed p4: for EVERY positive integer m,n, the literal q-Fibonomial polynomial is unimodal. This is the full target retained below, with old-target status explicit. Connelly et al. 2605.12822v1 Conjecture1.1 repeats it; Theorem1.2 and Section4 prove n<=3. Read actual original Theorem2.4 tiling proof, Conjecture2.5, and actual closest Section3 chain and Section4 algebraic proof bodies. Latest arXiv abstract records observed list original v3 and successor v1; the successor's internal manuscript date says August24 despite its v1 submission listing May12. We preserve both, not invent a new version.

Agoh Integers26 A9 final conjecture was fetched/read but immediately retired after the r23/r63/r64 prior exclusions were located. No fresh mechanism or repeat investment there. It is not an eligible fourth candidate.

## Closest new public proof body

Xiaojian Zeng, *Unimodality of the Fourth-Order q-Fibonomial Coefficients*, five-page actual PDF at ArtificialZeng/AI-Has-Taste revision f3ae144b74f238f22c2b84b5283cb14ce912fd33. Full theorem and all proofs read. Theorem1 covers every m>=1 with n=4 only. It reduces differences to four evaluations of the {1,2,3} denumerant, bounds its six-residue error, and treats six finite base cases. This is public and independently also excluded by our old B2 bridge. The paper expressly leaves the unrestricted two-parameter conjecture untouched. No authoritative earliest-publication time was established; only observed public availability, so no priority ordering beyond that is asserted.

## Full-scope algebraic route and its exact gap

Set F0=0,F1=1,F_(i+2)=F_(i+1)+F_i and

B_(m,n)(q) = product_(i=1..n) (1-q^(F_(m+i)))/(1-q^(F_i)).

This equals the literal q-integer quotient: the n factors (1-q) cancel. Original Theorem2.4 supplies polynomiality and nonnegative integer coefficients; it is public, uncredited. Its degree is

D = F_(m+n+2)-F_(m+2)-F_(n+2)+1.

Reciprocity follows from replacing q by 1/q in each factor, since numerator and denominator have the same number of factors. Write B=sum c_t q^t, c_-1=0. Unimodality is exactly delta_t=c_t-c_(t-1)>=0 for every 1<=t<=floor(D/2).

Let h_n(t) count nonnegative integer solutions to sum_(i=2..n) F_i x_i=t, with h_n(t)=0 for t<0. All such counts are finite since every weight is positive. In formal power series,

(1-q)B = product_(i=1..n)(1-q^(F_(m+i))) / product_(i=2..n)(1-q^(F_i)).

Expanding its finite numerator gives the exact all-parameter criterion

delta_t = sum_(S subset {1,..,n}) (-1)^|S| h_n(t - sum_(i in S) F_(m+i)).                 (A)

This derivation is rigorous for arbitrary m,n, but is a standard coefficient identity, not a source resolution. It implies the public-style easy initial range t<F_(m+1), since only the empty subset contributes. The required remaining interval is F_(m+1)<=t<=floor(D/2), whenever nonempty. For n=4, the Fibonacci additive cancellations and quadratic denumerant lead to the already-public proof. For arbitrary n the denumerant dimension and residue period grow; no uniform signed-sum bound was obtained.

A tempting generalization is false: nonnegative symmetric polynomiality, denominator weights F1..F4, and every numerator degree >=F5 do not ensure unimodality. The exact polynomial

[5]_q^3 [18]_q / ([2]_q[3]_q)

has coefficients

1,2,4,7,11,13,17,19,20,20,22,20,21,21,21,20,22,20,20,19,17,13,11,7,4,2,1.

Its 22,20,21 valley is below the center. It really is a positive polynomial: [18] supplies both [2] and [3], which are coprime; full integer recomposition is checked independently. Its degrees 5,5,5,18 are NOT consecutive Fibonacci numbers. Thus it refutes a weak proposed invariant, not the source.

## Source recurrence route

The original Theorem2.4 proof supplies exactly

B_(m,n) = [F_(m+1)]_(q^F_n) B_(m,n-1)
        + q^(F_n F_(m+1)) [F_(n-1)]_(q^F_m) B_(m-1,n),  m,n>1.             (B)

The summands are not centered at D/2. Termwise monotonicity through that center fails even for genuine source inputs: m=2,n=6,D=32, at t=16 the first summand decreases by 1 and the second increases by 1. The total difference is zero, not negative. Therefore a proof needs quantitative compensation, not merely induction on unimodality of smaller B. The source's two-row chain argument does not supply that all-n compensation. Forty-nine independently expanded recurrence identities pass.

A one-numerator-factor-per-denominator-factor cancellation route also fails. At m=9,n=4 the denominator F3=2 and F4=3 can divide only F12=144 among F10,F11,F12,F13=55,89,144,233. Their common neighbor set has size one, so Hall prevents an injective assignment. This does not prevent more general factorization or the known B2 proof; it only rules out this elementary matching route.

## Logarithmic derivative route

Let R=(1-q)B=sum delta_t q^t. Formal differentiation yields

t delta_t = sum_(j=1..t) L_j delta_(t-j),
L_j = sum_(i=2..n, F_i divides j) F_i - sum_(i=1..n, F_(m+i) divides j) F_(m+i).        (C)

This follows by geometric expansion of qR'/R, with R(0)=1. Positivity of all L_j would give an induction for delta, but genuine m=n=5 has L8=1+2-8=-5 while delta8=12. Hence log-coefficient positivity is unavailable. A weighted convolution domination sufficient for (C), uniform in m,n,t below the center, remains unproved. This is not evidence against the source conjecture.

## Registry and priority bounds

Used read-only complete inventories in root-edge-irregulator-current-prior-r1/CURRENT-REGISTRIES.json, UTC2026-10-29T17:20:12.045045+00:00. Omega revision70af54071bfd4ac098619a9db8c16bb6f7aced11 has350009 entries; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a has174524. Both tree SHA256 values are preserved in provenance.json. No git/cache mutation or git command was used. Actual matching QProduct Blueprint and Lean bodies were fetched by pinned raw HTTP and read, as was the Library note. These distinguish Conjecture5.4 from the full q-Fibonomial target. OpenAI current CONTENTS was text-screened; no full body-wide audit was made. Names alone do not clear absence or complete subsumption. These are dated snapshots, not current-head claims at handback. No API403/429 retries, proxy, or bypass; no API requests at all. No stale6c27 or Blueprint-only tree was used for current coverage.

## Validation, strongest objection, falsifier

Run `sh run.sh` offline. It checks 144 pairs with 1<=n<=m,m+n<=24, maximum degree120640; exact nonnegativity, symmetry, lower-half differences and value at1. Thirty-six small pairs are independently reconstructed by q-integer convolution and monic long division. Sixty-four coefficient difference identities,49 source recurrences,4529 Newton identities, sparse signed-denumerant comparisons, Hall obstruction and generic full recomposition pass. These overlap; none establishes the universal target. The old campaign already checked m,n<=12; these are replay/route checks, not new source evidence of a resolution.

All Python helpers use the copied recent guard: AS512MiB; process-group sampled RSS512MiB; CPU210s; wall230s;40ms sampling; BLAS threads1. Peak recorded runs are far below the cap. Unsampled transients are not ruled out. No cap increase. Source406, web unsupported-DVI, pdftotext missing-file warning, and late reconciliation deviations are retained in failures.md.

**Strongest objection:** the target is an older unresolved family, and the substantive required uniform inequality is still missing. Neither rebranding a public n4 proof, a familiar coefficient identity, a finite scan, nor a generic obstruction earns credit. There is no complete ordinary proof or counterexample and no substantive clearance.

**Decisive falsifier:** any positive m,n and integer1<=t<=floor(D/2) for which the literal quotient has delta_t<0, certified by exact coefficient recomposition. Conversely, a genuine uniform proof of (A)'s nonnegativity (or compensation in (B)/(C)), together with a current bounded prior/subsumption review, would resolve the full target. No such sign theorem is asserted here.
