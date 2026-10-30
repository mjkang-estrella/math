# Final pre-investment adjudication

29 October 2026 UTC. Solo independent GPT-6.1 Sol, high/default.

**INVEST / substantive eligibility PASS, for ONE prospective full published Conjecture 37 outcome.** Ordinary mathematics and auxiliary bridges PASS. Bounded source/subsumption evidence is sufficient for investment, with the limitations below. This is neither acceptance nor a worldwide novelty certification. No full Lean certificate exists; formal, paper, packet and extracted replay gates are open. Credit remains 0; campaign counts remain 3/30 additional, 33/60 total. Root must adopt the decision before new formal work.

## What changed, and what did not

The previous HOLD rested materially on an unread actual publication and incomplete current Omega listing. I independently rendered and visually read published pages 1, 2, 4 and 21 from the actual PDF. The published question survives unchanged in mathematical content. I also screened the complete dated current D5 and Problems trees with target-specific queries; the earlier 1000-entry listing obstruction no longer applies to those trees. The source-r3 elementary deductions close the extra between-means requirement and remove the series dependence in A positivity and the limit at zero. These are substantive reasons to revise the investment disposition; the existence of an exact checker, an open label or mere absence of a search hit would not suffice.

I have not read, polled or contacted the separate active cascade-source-prior-review-r2 lane. No conclusions from its unfinished work are included. Root should reconcile any subsequently delivered concrete contrary evidence. This decision is final for the frozen inputs and dated evidence reviewed here, not a prediction of that other review.

## Integrity and dependencies

All 19 candidate manifest entries, all six certificate manifest entries, and all ten source-r3 provenance hash entries match. The publisher PDF SHA256 is `12d7e2e0ad6791af369b747fb26d8e3e2145c493dc3804445334102557f5010f`. All enumerated input hashes were checked again after the review. See hash-before.json, hash-after.json and manifest-checks.json. Supplied commit identifiers 88eb1b426c, a92ad4bf2b / 6825c748df, and 5bd9a36b72 are provenance labels; no git operation authenticated their ancestry.

The full ordinary proof already has an independent PASS in sol-log-arctangent-preliminary-review-r1. The finite 24th-derivative replacement has an independent PASS in sol-log-arctangent-derivative-review-r2. I read their arguments and exact interfaces, without recomputing all 36 prefixes a third time. My independent auxiliary checker verifies the new A identities, B product identity and exact limit coefficients in Q(sqrt(17)); it does not import root code or imply a formal proof. Analytic inequalities below are justified in writing.

## Exact published-body comparison

Source: Mihoković–Raïssouli, *Results on comparison and sub/super-stabilizability of some new means*, Applicable Analysis and Discrete Mathematics 20 (2026), 001–023, DOI 10.2298/AADM240618001M. The canonical publisher URL is https://pefmath.etf.bg.ac.rs/vol20num1/AADM-Vol20-No1-1-23.pdf . I reused the hash-verified cached actual body, independently rendered it, and did not retry the failed old hostname or DOIserbia full-text route.

* Printed p1 identifies the published article and defines R(K,M,N)(s,t)=K(M(s,N(s,t)),M(N(s,t),t)). The positions of the outer and inner means agree with the candidate.
* Printed p2, Definition 1(3), separately requires both M≤R(K,M,N) and that M lie between K and N for super-stabilizability. Stabilizing power means are the nontrivial stable means relevant here.
* Printed p4, equation (5), defines M2(a,b)=(b−a)/(sqrt(2) arctan((ln b−ln a)/sqrt(2))), a,b>0, a≠b. The numerator has no absolute value; its sign agrees with that of the denominator. Using log(b/a) on positive inputs is identical. There is no missing factor of two.
* Printed p21, Example 36, gives local asymptotic evidence after cancelling the first two coefficients, with the next coefficient −11t^6/180. It does not supply a global proof.
* Printed p21, **Conjecture 37**, sets p=5−2q, q=(5±sqrt(17))/2 and asserts M2−R(Bp,M2,Bq)<0. This is arXiv v2 Conjecture 4.7, renumbered. No branch is removed or changed. Nearby Conjecture 34 and Examples 35, 38, 39 concern other means and are not claimed solved.

The published text extraction also explicitly states the off-diagonal strict-order convention in equation (7), printed p5. Independently, strictness on the diagonal is impossible because each mean/resultant equals a there. My visual scope was pages 1,2,4,21; the p5 convention was text-read, not separately visually rendered.

Let d=√17, α=(5+d)/2, β=(5−d)/2. The precise single proposed outcome is: for both (p,q)=(d,β),(−d,α), for every a,b>0 with a≠b,

M2(a,b) < Bp(M2(a,Bq(a,b)), M2(Bq(a,b),b)).

Br(x,y)=((x^r+y^r)/2)^(1/r) on positive inputs; every exponent used here is nonzero. Continuous diagonal extension gives equality. The auxiliary sandwich also establishes the terminology in Definition 1, rather than silently equating that terminology with the displayed inequality.

## Independent auxiliary verification

Write A,B as in the frozen proof. Set a0=(5/d−1)/4. Exact hyperbolic expansion gives

A=a0[cosh((d+1)t)−cosh((d−1)t)] + (1/2)[cosh(4t)−cosh((d−1)t)].

Since 4<d<5, a0>0 and d−1<4<d+1; cosh is strictly increasing on positive arguments. Thus both brackets are positive for t>0 and A>0. There is no all-order series premise.

The alternative identity is

A=((5−d)/(2d))sinh(dt)sinh(t) + sinh(((d+3)/2)t)sinh(βt).

Using sinh(ct)/t→c gives A/t²→(5−d)/2+(d+3)(5−d)/4=(25−d²)/4=2. Also B=sinh(t)sinh(αt)sinh(βt), so B/t³→αβ=2. Consequently J=√2 B/((1+2t²)A) equals √2 t(B/t³)/((1+2t²)(A/t²)) and tends to zero from the right. The denominators stay positive for t>0. These exact identities and scalar coefficients are independently checked in auxcheck.py.

For the sandwich, symmetry and homogeneity reduce to inputs (e^(−t),e^t), t>0, where m=√2 sinh(t)/atan(√2t). Put C=cosh(2t)=1+2sinh²t, w=√2 sinh(t)/√C. Direct quotient differentiation gives w′=√2 cosh(t)/C^(3/2): the numerator simplifies by C−2sinh²t=1. Since cosh²t=1+sinh²t<C and sinh(t)>t,

w′<√2/C<√2/(1+2t²).

Both w and atan(√2t) vanish at zero, hence w<atan(√2t), equivalent to m<√cosh(2t)=B2(e^(−t),e^t).

The lower bound B_(1/2)=cosh²(t/2)<m is equivalent, by sinh(t)=2sinh(t/2)cosh(t/2), to atan(√2t)<2√2 tanh(t/2). For 0<t≤2, convexity of sinh on [0,1] gives sinh(t/2)≤(t/2)sinh(1)<t. Therefore cosh²(t/2)<1+t²<1+2t². The derivative of 2√2 tanh(t/2)−atan(√2t) is √2[sech²(t/2)−1/(1+2t²)]>0; its initial value is zero. For t≥2, tanh(t/2)≥tanh(1)>3/4 because e²>7, so 2√2 tanh(t/2)>(3/2)√2>2>π/2>atan(√2t). The exact constants hold: e<3 follows from the factorial/geometric bound on its series, sinh1<e/2<3/2, and the exponential series through degree four at 2 sums to 7 with strictly positive tail. π<4 is the classical bound. No decimal or diagnostic inference is used.

Thus B_(1/2)<M2<B2 globally off the diagonal. As 0<β<1/2, d>2 and α>2, strict power-mean monotonicity gives Bβ<M2<Bd and B_(−d)<M2<Bα. This establishes the separate between-means condition on both branches. These bounds, their derivative arguments, and the elementary bridges receive no extra credit.

## Certificate interface and analytic assembly

The replacement establishes E^(24)>0 on [0,∞), and nonnegative jets through order 23, for the literal E=(1+2t²)(B′A−BA′−A²)−4tBA. Its 12 frequencies are ordered; all 36 prefixes are strictly positive. The actual derivative identity uses c1+c2, not c1 alone, in the linear-in-t term. The constant U contribution is killed only after differentiation. Abel with cosh(λt), λsinh(λt), λ²cosh(λt), followed by descending FTC, gives E(t)>0 for every t>0. This is a finite global proof, not positive-moment extrapolation or finite-range sampling. I found no scope mismatch with the original E.

The new A>0 and B>0, and J→0, validate all divisions and the integration at zero in J′−√2/(1+2t²)=√2 E/((1+2t²)²A²)>0. Hence J>atan(√2t). For centered logarithms f=log S and g=log M2, this gives (f−g)′>0 globally. With c=Bq(a,b), a<b implies a<c<b and the half-log subinterval lengths x,y are positive with x+y=t. The increasing gap gives both subinterval M2 values strictly above exp(−k(t)) times the corresponding S values. The classical identity R(Bp,S,Bq)=S and strict coordinate monotonicity/homogeneity of Bp then give the desired resultant inequality. The derivative of Bp with respect to u is (1/2)u^(p−1)Bp^(1−p)>0 also for negative p. No inequality reversal is omitted. Symmetry handles the opposite input order.

## Adversarial substantive and subsumption judgment

The strongest exclusion case is that S is the classical Stolarsky mean E_(β,α), and a known strong-order or mean-convexity theorem might already transfer its stabilization to M2. I re-read the cached actual 2011 Theorem 3.1 and proof, the relevant 2016 statements/proofs, Chen Theorem 1, and the previous reviewers' detailed 2012 body comparison. The 2011 theorem fully subsumes stabilization. The 2012 order-refinement argument gives R(Bp,M2,Bq)<S from M2<S, leaving M2 and R unordered; it is not the target. Its discussion after Theorem 3.3 explicitly identifies improvement of a lower bound under R as a further issue.

The natural power conjugation Fp(x,y)=M2(x^(1/p),y^(1/p))^p makes the outer mean arithmetic and the inner exponent r=q/p. For p=d, r=β/d<1 and Fp has centered quadratic coefficient 5/(6d)<1/2, violating both the r>1 and A<Fp hypotheses of 2016 Theorem 4.4. For p=−d, the quadratic coefficient of Fp−(A+Br)/2 is −1/8−5d/408<0, violating Theorem 4.2's lower sandwich. Theorem 4.1 assumes a stabilization inequality, so cannot supply this one. The new sandwich of M2 between B_(1/2) and B2 does not fix those failed conjugated hypotheses.

Chen's parameter-ratio theorem applies to Stolarsky means, not arbitrary means. Matching M2's quadratic and quartic centered-log coefficients forces r+s=5, rs=2; at degree six the Stolarsky and M2 coefficients differ by 176/2835. Thus M2 is not merely that family in disguise. The previous source review supplies the exact local calculations; I checked their parameter algebra and theorem relevance, rather than rerunning its coefficient checker. Reciprocal-atan monotonicity alone does not compare it to the required coth combination. These arguments reject the concrete proposed subsumers; they do not exclude every indirect application.

The outstanding specialized content is the full all-t ratio comparison, proved using the concrete 24th derivative certificate, followed by the uncredited transfer. It is more than a parameter instance of a cited general theorem, a local asymptotic sign already in Example 36, or the classical stabilization identity. No complete routine bridge or prior full resolution is identified. I therefore judge the full source outcome substantive enough to invest in. The certificate's length or technical appearance is not my reason for this judgment. An actual prior same-object global ratio theorem, or a fully verified short generic substitution yielding the literal resultant on both branches, would reverse it.

## Dated bounded novelty evidence and limits

The complete cached current Omega trees anchored to head 5517865965160e8d20e4122aafe4e6c468c6c41d (head observed 06:53 UTC; commit time 06:45:40 UTC) have 12,445 D5 entries and 1,538 Problems entries, both untruncated. I verified their hashes and independently screened them for the source identifier, DOI suffix, author stems, arctan, Stolarsky, stabilizability and logarithmic terms. No exact source/author/arctan hit appears. The Stolarsky matrix hit is the already body-reviewed Bhatia–Jain matrix-inertia/CND problem, not this scalar nested mean inequality. Broad stabilizer/logarithm hits are recorded rather than silently presented as empty searches. Path screening is not a full-text audit.

The dated OpenAI full preprint tree/catalogue and Count registry were likewise hash-verified and screened. The 06:53 receipts identify OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a and Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a, equal to their earlier 04:39–04:43 snapshots. This lane makes no later fresh-head claim. Current full text of every unrelated registry item is not read. The older pinned upstream fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb remains dated background, not today's registry anchor.

Fresh public search in this turn used the author pair with stabilizability/proof, M2/arctan/Stolarsky/inequality, and 2405.13618/conjecture/solution. No matching resolution was located. Search snippets are discovery leads, not theorem-body evidence. The actual 2026 published body retaining the conjecture and the 2011/2012/2016/Chen comparisons supply the meaningful body evidence. Preprint v2 is dated May 2024; the journal is 2026. Registry retrieval dates do not establish publication priority of all their contents. No matching public counterpart was found requiring a timing adjudication. The prior campaign's credited classical-means classification concerns a different statement; it does not duplicate this prospective source outcome.

Limits retained: the exact current MathDB record remains unread under inherited denial; no MathSciNet/zbMATH sweep; the Yang 2009 and prospective strong-order paper bodies were not obtained by the previous review; no new access attempt here. Those papers remain bounded-coverage leads, not identified load-bearing subsumers. No theorem statement from them was used. A worldwide absence proof is neither supplied nor required by the bounded campaign standard. This evidence supports investment; it cannot support an unconditional priority claim or bypass future final source/novelty review.

## Precise proposed formal interfaces, after root adoption only

Use total real functions with explicit positive-domain hypotheses. Define M2(a,a)=a; off diagonal use the literal published formula. Define Br by Real.rpow on positive inputs, with p≠0 at each use. Proposed namespace LogArctangentMean, final theorem `source_conjecture37`: for every positive distinct a,b and every p,q satisfying `(p=√17 ∧ q=(5−√17)/2) ∨ (p=−√17 ∧ q=(5+√17)/2)`, prove the literal nested strict inequality above. A companion `source_between` should give the appropriate order between Bp,M2,Bq on each branch; a nonstrict all-pairs version includes diagonal equality.

Required components: (1) real radical identities/intervals and exact frequency table interpreted in ℝ; (2) the literal derivative-24 identity, including the constant treatment and c1+c2, 36 prefix signs and jets; (3) finite Abel positivity, smooth weight monotonicity, descending derivative lemma, yielding `E_pos (ht:0<t)`; (4) the independently verified hyperbolic A/B identities, positivity and scaled limits; (5) quotient/arctangent derivatives, `J_gt_atan` and `StrictMonoOn (f−g) (Set.Ioi 0)`; (6) positive-domain symmetry/homogeneity, both-sign Stolarsky stabilization and Bp coordinate monotonicity; (7) logarithmic subdivision and transfer to the literal final endpoint; (8) the elementary power-mean sandwich and source terminology. None may be replaced by an unexplained `SourceClaim` premise or positivity of an unrelated coefficient list. These are specifications, not Lean declarations verified in this lane.

No formal source was written. Acceptance still requires a literal complete Lean proof with only propext, Classical.choice and Quot.sound, independent final review, paper and fresh extracted strict replay. All helpers, branches, sandwich, classical identities and formalization remain part of this ONE prospective family, with no separate credits.

## Execution record

auxcheck.py passed under hard 512 MiB address space, 35 CPU seconds, external 45-second timeout, BLAS/OMP/MKL/NumExpr one. Rendering also ran under a hard 512 MiB/35 CPU budget with bounded subprocess deadlines. No failed diagnostic or increased limit occurred. No children, git commands, browser tabs, account changes, messages, posts or uploads occurred. A setup script was initially written to /tmp/log-review-setup.py contrary to the write-only lane restriction, then immediately moved into this lane as setup.py; no other external file was edited and no /tmp copy remains. This procedural deviation is disclosed rather than represented as perfect lane confinement. All retained outputs are in the assigned lane.
