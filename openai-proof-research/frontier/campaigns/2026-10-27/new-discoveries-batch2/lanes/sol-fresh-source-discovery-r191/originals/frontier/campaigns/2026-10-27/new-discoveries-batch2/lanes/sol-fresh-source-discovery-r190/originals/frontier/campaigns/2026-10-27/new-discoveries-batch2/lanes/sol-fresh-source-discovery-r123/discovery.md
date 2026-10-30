# No substantive fresh resolution nominated

Research date29October2026UTC. Solo GPT6.1Sol high/default speed. Assigned
lane only. Credit0; observed9additional/39total is context, not a count edit.
No formal or manuscript investment. No PROOF.md because no eligible full
candidate survived. All claims below distinguish mathematical scope from
eligibility and from external-public-proof authentication.

## History and selection discipline

Read ancestor/batch AGENTS, source pin/catalogue, required root dispositions,
r120 SUMMARY/discovery, relevant ledger entries and actual reused registry
reviews. Large combined initial console output truncated; byte copies and
specific subsequent reads are retained. I do not assert full semantic reading
of every ledger/catalogue/tree entry. Shared NEXT was captured separately as
coordination-NEXT-as-read.md with its own receipt, never a mathematical freeze.

Before selecting a surviving target, streamed all dates under
openai-proof-research, original research/rejections/copied reviews/catalogues
and scripts, using SHA256 deduplication and compressed hash-to-path mapping.
377975 selected paths represent275923 distinct bodies. Six900-character broad
excerpts per body, with no global hit cutoff;942 matching bodies. A second
target stream gave790 bodies/2527 lines, at most five1100-character excerpts
per body, no global hit cutoff. Reports and aliases led to the actual reads
below. This is retrieval, not comprehensive semantic coverage. The focused
report filters those bounded excerpts and can miss later terms in a body.
Generic Conjecture7.1, numeric03505 and boundary-contact terms produced noise.

Exact exclusions and70 size/aggregate gap paths and sizes are in
screen-receipt.json. Selected text extensions are explicit; PDF/binary and
compressed bodies are unsearched unless separately extracted. Dependency/build
directories and listed generated content-echo basenames are excluded. Files
over12MB and matching r111–r113 aggregate patterns are skipped. Other small
generated index/echo files were scanned and are noise, not independent evidence.
New SQLite stores hashes/representative paths, not duplicated source contents;
no giant new content cache was generated. Public proofs and old exclusions
were stopped as discovery leads, rather than recycled as new targets.

## Xu–Yang: complete routine route, no nomination

Actual publisher PDF: Hui-Zuo Xu and Zhen-Hang Yang, *Higher order monotonicity
involving the Mills ratio with applications*, J.Inequal.Appl.2026:98,
DOI10.1186/s13660-026-03505-9. Published19June2026, VoR31August2026 per
publisher metadata. PDF definitions1.1/1.8, Theorem3.1 and3.3, their actual
kernel derivation, Corollary4.2, full Theorem4.2 proof including Lemma4.1,
and actual Conjecture7.1 on printed p27 were read. The earlier Mills review
already names this different conjecture; no earlier new-result claim is made.

Let R(x)=integral_0^infinity exp(-xs-s²/2)ds, x>0, and
Y_(a,b)(x)=(x²+a)R(x)²+bxR(x). The source defines coefficients u_k(a,b) by
its asymptotic series3.6–3.7 and D_n(x,a) by subtracting
a-1+sum_(k=1)^n (-1)^k u_k(a,a-2)/x^(2k) from Y_(a,a-2).
Its Conjecture7.1 says (-1)^n D_n(x,-1) is completely monotone.
The printed paragraph does not explicitly specify the lower index bound.
Its surrounding Theorem4.2 treats n=2,3,4. The argument here covers every
integer n>=2 and every x>0 and every derivative order ell>=0. It does not
silently claim the literal extension to n=1: u1=u2=0 and D1=D2>0, so that
(-1)D1 is negative. An index-convention/wording correction receives no credit.

Here is the entire analytic route, to expose the routine objection rather
than leave a numerical all-order gap. Put f=Y_(-1,-3)+2. The source's own
convolution kernel, after u=s(1+v)/2, gives f(x)=integral e^(-xs)k(s)ds with

 k(s)=s{integral_0^1 [s²(1-v²)/4-1]e^[-s²(1+v²)/4]dv+e^(-s²/2)}.

Write z=s² and E(v)=exp[-z(1+v²)/4]. Integrating (vE)' on[0,1] replaces
the final exponential by integral(1-zv²/2)E. Combining terms leaves
z/4 integral(1-3v²)E. A second integration by parts, using
(v-v³)'=1-3v² and its zero boundary values, yields exactly

 k(s) = s^5/8 integral_0^1 (v²-v^4) exp[-c(v)s²]dv,
 c(v)=(1+v²)/4 in[1/4,1/2].

For each j>=0 the Laplace integral of its j-th Taylor monomial is

 (-1)^j (2j+5)!/(8j!) integral_0^1(v²-v^4)c(v)^j dv / x^(2j+6).

These are the source coefficients (-1)^(j+3)u_(j+3)(-1,-3).
One can identify them without assuming convergence of the asymptotic series:
for any fixed J the integral Taylor remainder has absolute value at most
(c s²)^(J+1)/(J+1)!, giving an integrated O(x^(-2J-8)) bound. Finite
asymptotic expansions have unique coefficients. The two missing coefficients
u1=u2=0 agree with3.7. The exact rational checker independently compares
the displayed mixture moments with3.7 for n=3..42; this is corroboration,
not an all-index identity proof by finite checks.

For n>=2 put m=n-2. D_n is the Laplace integral of s^5/8 times
the positive v-weight times

 E_m(y)=exp(-y)-sum_(j=0)^(m-1)(-y)^j/j!, y=c(v)s²,

with the sum empty if m=0. For m>=1, Taylor's integral formula gives

 (-1)^m E_m(y) = 1/(m-1)! integral_0^y exp(-r)(y-r)^(m-1)dr >0 (y>0).

For m=0 it is simply exp(-y)>0. Since (-1)^m=(-1)^n, the signed kernel
is strictly positive for all s>0 after v-integration. For fixed m>=1 its
growth is bounded by a polynomial in s (and for m=0 it decays). Hence for
every fixed x0>0, multiplication by any s^ell and e^(-x0s) is integrable.
Dominated differentiation on x>=x0 gives

 (-1)^ell d^ell/dx^ell [(-1)^n D_n(x,-1)]
 = integral_0^infinity s^ell e^(-xs)[(-1)^n remainder_kernel(s)]ds >0.

This covers the natural all-order range, not just selected n or derivative
orders. No uniform estimate as n or ell tends to infinity is needed for the
quantifiers defining complete monotonicity. There is no hidden uniform
analytic gap in this route.

**Strongest objection, adopted:** the source already represents the exact
object as a Laplace kernel and proves its low-order truncation signs by
subtracting Taylor monomials. At a=-1, the two elementary integrations by
parts above expose a positive Gaussian mixture. The classical exponential
Taylor remainder then gives every order without another structural lemma.
This is a routine adaptation under the campaign standard, even if no printed
all-order application is located. Shortness or elementary tools alone are
not the objection; the complete explicit bridge is. Falsifier: a concrete
failure in those identities, coefficient identification, or integrability,
or a genuinely additional nonroutine ingredient. A new paper/formalization,
index extension, or the printed lower-index ambiguity does not suffice.
Formal feasibility: finite-interval IBP, positive integrals, Gamma moments,
Taylor remainder and dominated parameter differentiation would implement
the route. No Lean endpoint or library-readiness certification is asserted.

## Other actual-body screens and exclusions

1. **Ferreira–Simon2108.09244v2.** Actual primary PDF retained. Read
   Proposition1/Corollary1 proofs, Remark2(d), Conjectures1–3 and the
   surrounding representations, Proposition10/11 and their proofs. Conjecture1
   is all a>0,0<b<1/2 independent beta-prime addition. Ledger explicitly lists
   root-beta-prime-addition-r19, with actual review and root adoption: Durand1978
   negative-order product substitution supplies the conditional inverse-Gamma
   identity and beta–Gamma split. Read that full recorded bridge and adoption;
   did not claim a new visual reading of the Durand journal page. Its preserved
   source-access caveat remains. Conjecture3 is already credited Mills ratio;
   not recounted. Conjecture2's registry search lead is not used as a theorem
   without proof-body verification and is not nominated.

2. **Noncentral chi-square HCM.** Actual Salazar2606.22066v1 PDF retained,
   dated20June2026. Read Theorem1, Proposition2's entire small-u Bell argument,
   Lemmas1–2 and full final proof. HCM would make all Taylor coefficients of
   e^(bt)0F1(;a;-b theta t) nonnegative. Its positive Bessel zero contradicts
   positivity of an entire series with constant coefficient1. This is an
   actual public full positive-noncentrality exclusion, not an abstract badge.
   No claim of fresh resolution. The initiating BPV publisher statement was
   only attributed through the public proof's source discussion; original
   BPV body was not retrieved in this lane.

3. **Krasniqi2609.28707v1 Conjecture23.** Actual primary PDF retained; read
   Proposition3's density statement, Lemma13/14 proofs, Theorem17 and proof,
   Corollary18, Proposition21 and proof, and actual Conjecture23. For every
   -1<b<0 it asks for exactly one positive zero of D_(A(b),-b), of order two.
   The source itself supplies only finite nonempty contact set and even
   multiplicity; the conditional IFT theorem assumes the missing conclusions.
   These are not an unconditional uniqueness argument. Toy nonnegative
   polynomials with two double contacts or one quartic contact illustrate
   only why analyticity/nonnegativity is insufficient. They do not satisfy
   the source's Volterra equation and are **not source counterexamples**.

   History then supplied actual public KrasniqiBoundaryContact.md, already
   read/excluded in r5 and r97. Fetched the full body at fixed r119-observed
   a7769c3, SHA256 b336416f4a6fb465f94d76c3fd2c55607f0c2b6554d7c0328afab29723b2edbb,
   identical to the old cached body. Read Theorem2.2 and3.1 proof bodies,
   particularly the two-switch case: K=D''-(r+R)D'+rRD has a claimed uniform
   positive bound via a238-box rational certificate; J=e^(-Rt)(D'-rD) is
   then strictly increasing, so there is at most one contact and D''>0 there.
   The other cases use one-switch variation and Rolle. This is exactly the
   full source quantifier. I did not independently regenerate the238-box
   arithmetic or replay public Lean, so this is exclusion by an actual
   public proof, not a new independent certification. Full proof body and
   all partition data retained. r5 records the posting commit b297c2a7... at
   3October2026 22:45:27UTC; this dated historical attribution was read,
   not freshly queried. Public proof demonstrably predates this research;
   no worldwide-first claim. The separate endpoint question was already
   attempted in r5 and is not recycled.

4. **Bondesson–Steutel2004.** PDF request returned403. Exact response bytes,
   URL/date/hash retained. No alternate-host retry or bypass. The search lead
   is not a body-verified fresh problem, and no novelty conclusion is drawn.

## Registry chronology, remaining gaps and delivery

Actual retained r4 review/exactcoverage closes fixed0d4df45→d254db by9
first-parent steps,28commits,538paths. Actual factorial final review and
fresh-coverage closes12steps throughc3e8754. r119's22:21:24 observation is
a7769c386bd6072628a21cf4680756d2a49bf221; d254→a776 has47commits/207paths,
uncapped but not all-body semantic clearance. OpenAI7ef5c0cc... is inherited
unchanged. These receipts concern mainline states and selective baseline
semantics, not every transient sidebranch or every mathematical equivalence.
No API cap is treated as complete. No new HEAD query or indefinite chase:
only the meaningful exact Krasniqi proof body was refreshed at that fixed head.
No global current-registry novelty clearance for Xu–Yang is claimed or needed
for a strict routine exclusion. Earlier independent public counterparts and
our own credited Mills publication are not automatically treated as earlier
than their own creation; no chronological priority competition is asserted.

No fresh full-scope substantive candidate remains. This is a failed discovery
search, not a claimed new theorem, unresolved-source counterexample, helper
nomination, or parameter result. The only completed ordinary route is routine;
the other plausible source gap is already publicly closed. The precise
remaining barrier is eligibility/freshness, not concealed numerical evidence
for an all-scope proof. No unsupported uniform gap is invented for an already
closed source question. No future endpoint/helper project is recommended here.

run-check.sh uses the unchanged prescribed helper guard. All helper/Python
executions and Poppler extraction used it; native bounded reads/apply_patch
were used directly. AS/groupRSS512MiB,CPU210s,wall230s,nominal40ms,BLAS1;
no cap raised. Scan guard reports197.13s/47.3MB sampled groupRSS and target
scan122.53s/43.8MB, both exit0. Sampling is not a continuous peak guarantee.
Checks give40 exact rational coefficient comparisons plus kernel identities
and retained HTTP byte hashes. Finalmanifest binds all lane artifacts except
itself and its verification receipt, whose manifest digest is separately
verified. No shared files, git, children, polling other agents, browser,
accounts, messages, posts, uploads or external mutations.
