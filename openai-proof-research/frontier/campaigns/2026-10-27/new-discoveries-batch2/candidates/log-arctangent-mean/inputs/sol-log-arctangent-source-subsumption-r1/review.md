# Independent source and subsumption review

Review date: 29 October 2026 UTC (28 October Pacific). Assigned source/subsumption lane only; no children, git commands, shared edits, browser tabs, external mutations, Lean work or acceptance. Root freeze commit `88eb1b426c` is the user's supplied identifier, not independently checked by git. The 19 manifest-listed candidate files were independently SHA256-checked before copying and after review. The freeze manifest itself is additional metadata, not one of those 19 files.

**Disposition: HOLD on published-source identity, substantive eligibility and novelty. No concrete classical theorem implying the full target was established. Stabilization alone is classical and excluded.** This is independent of the separate finite-plus-tail mathematical review. Preliminary root notes were read as context, not adopted as verdicts.

## Gate decisions and exact scope

| Gate | Decision | Scope |
|---|---|---|
| Frozen-file integrity | PASS | All 19 listed SHA256 values agree before and after; own byte copies only. |
| arXiv source identification | PASS | Actual cached v2 Definition 1.1, equation (1.5), Example 4.6 and Conjecture 4.7 read. Exact two-branch strict resultant inequality, positive distinct inputs. |
| Actual journal/accepted-source comparison | HOLD | No actual AADM 20(1)(2026), 1–23 VoR or accepted manuscript obtained. No assertion of unchanged Conj4.7 numbering, wording or definitions. |
| Classical stabilization as an outcome | FAIL | Direct instance of Raissouli 2011 Theorem 3.1, both branches. Already acknowledged by candidate. |
| Classical subsumption of full inequality | HOLD | Read theorem bodies give stabilization/order refinements, not the requisite self-comparison. Direct 2016 conjugation routes have exact local obstructions. No exclusion bridge found, but the bounded investigation is not exhaustive. |
| Substantive discovery eligibility | HOLD | Full global ratio comparison would be substantive relative to the bodies examined; no independent eligibility PASS without journal comparison and remaining novelty coverage. Elementary form alone does not justify exclusion. |
| Current bounded prior-art screen | HOLD | Fresh heads and bounded current material screened; no located same target. Omega current Problems web listing is incomplete; MathDB access remains blocked. No worldwide or complete registry clearance. |
| Analytic transfer from increasing gap | PASS, conditional | Given strict increase of k, stabilization and positivity, the resultant inequality follows for both signs of p. This is not a PASS for global k'>0. |
| Global finite/tail mathematical proof | HOLD / outside assignment | No duplicate certificate replay undertaken; separate math reviewer owns this gate. Local exact evidence here proves neither E(t)>0 nor the full conjecture. |
| Literal formal certificate | HOLD | No literal Lean endpoint supplied or reviewed; no formal PASS. |
| Acceptance/paper/packet | HOLD / not adjudicated | No acceptance, integration, publication or count action. |

## Literal source and missing publication comparison

In arXiv v2, M2(a,b)=(b-a)/(sqrt(2) atan((log b-log a)/sqrt(2))). Conj4.7 sets q=(5±sqrt(17))/2 and p=5-2q and asks M2-R(Bp,M2,Bq)<0. Definition 1.1 defines the resultant with the inner Bq and the outer Bp in precisely that order. The candidate's (p,q)=(d,beta),(-d,alpha) is identical. The source strict assertion is read off-diagonal: every mean and its resultant agree on the diagonal. Definition 1.1 also includes a between-means condition in its *terminology* of sub/super-stabilizability. This review certifies identification of the displayed inequality only, not an additional global sandwich assertion merely from that terminology.

The saved arXiv body SHA256 is `ca5e87dcd0cc54c69dfeb7f69e58b118bbb4071ab5270d2c06fe55a292a8b193`. Publication metadata and author listings are not substitutes for reading the actual publication. Fresh searches located the journal issue, JSTOR record and author listing; none delivered a body. The FER author page lists the 2026 article but supplies no attached accepted manuscript in its article entry. EMIS's proposed AADM URL was inaccessible; the separate Serbian electronic-library URL was also inaccessible. CroRIS timed out; JSTOR was inaccessible. Inherited DOIserbia/pefmath timeouts and certificate failures were not retried and TLS validation was never disabled. No account or author contact was attempted. A redundant web request to the Serbian electronic-library landing page occurred after its earlier tool failure; it again returned inaccessible and was stopped. This was a procedural deviation, not a successful acquisition or a bypass.

## Concrete classical bridge: stabilization is fully subsumed

Read actual Raissouli, *Stabilizability of the Stolarsky mean and its approximation in terms of the power binomial mean* (received 25 May 2011), Theorem 3.1, pp4–5 and proof: E(u,v) is (B(v-u),Bu)-stabilizable for all real parameters. This is the [saved primary PDF](https://rgmia.org/papers/v14/v14a43.pdf), SHA256 `4a64741d335f494b065eae9edc84e5b7a713f41ab2e169312da52b7853e76310`.

Take (u,v)=(beta,alpha), then swap u,v for the second branch; symmetry gives the same S=E(beta,alpha). Both u,v are nonzero and unequal, so no limiting case is needed. With c=Bq(a,b), c^q-a^q=b^q-c^q=(b^q-a^q)/2. For r=p+q,

S(a,c)^p=2q/r (c^r-a^r)/(b^q-a^q),
S(c,b)^p=2q/r (b^r-c^r)/(b^q-a^q).

Averaging cancels c^r and gives S(a,b)^p. Injectivity of positive real powers establishes the identity even for p<0. `independent_bridge_check.py` verifies the parameter relations in Q(sqrt17) and the symbolic cancellation independently. This identity has no discovery eligibility.

For the transfer, write t=log(b/a)/2=x+y, with x,y>0 the half-log subinterval lengths. Increasing k implies M(a,c)>exp(-k(t))S(a,c), and likewise on (c,b). Every Bp is strictly increasing and homogeneous on positive arguments: its partial derivative is (1/2)u^(p-1)Bp(u,v)^(1-p)>0. Thus R(Bp,M,Bq)>exp(-k(t))S=M. No reversal occurs in this monotonicity argument for negative p. What remains substantive is proving k strictly increasing globally, not this transfer lemma.

## Why the read classical refinements do not settle the target

Read actual 2012 *Refinements for mean-inequalities via the stabilizability concept*, Theorems 3.1, 3.2, 3.3 and proofs from the [saved full body](https://link.springer.com/article/10.1186/1029-242X-2012-55), SHA256 `f0d880fd8826820727f69785617b3cbb3e0119e4a613aa9eb08b705b673c824a`. Thm3.1 is strict resultant order monotonicity. Thm3.2 refines a sandwich around a stabilizable mean. Thm3.3 sends lower/upper bounds of a stabilizable mean through R to obtain other bounds of that mean. Applied with m=S and lower bound M, it gives R(Bp,M,Bq)<S. Combined with M<S, this does **not** order M against R. The paragraph immediately after Thm3.3 explicitly asks what extra conditions make m3<R(m1,m3,m2); that is the missing comparison here. This prevents treating generic order monotonicity as a complete subsumer.

Read actual Raissouli–Sandor 2016 *Sub-super-stabilizability of certain bivariate means via mean-convexity*, Theorems 4.1, 4.2, 4.4 and proofs, [saved full body](https://link.springer.com/article/10.1186/s13660-016-1212-z), SHA256 `f678c7be4ce7df489f9fe8dcb1883e77de37490f4754400fe6bc205a551eaae6`. Thm4.1 assumes a stabilizability inequality; it cannot supply it without circularity. Thm4.2 requires strict concavity and (A+Br)/2<=F<A, r<1, to give R(A,F,Br)<F. Thm4.4 requires strict convexity and A<F<=(A+Br)/2, r>1, to give the opposite comparison.

The natural exact outer-power conjugation is Fp(x,y)=M(x^(1/p),y^(1/p))^p and r=q/p. It converts the candidate comparison to R(A,Fp,Br)>Fp for p>0 and <Fp for p<0. Independently expanding log M(e^-t,e^t) gives (5/6)t²-(7/12)t⁴+(287/405)t⁶+O(t⁸). Hence log Fp(e^-t,e^t) has quadratic coefficient 5/(6p). For p=d it is below A's coefficient 1/2, contradicting Thm4.4's necessary A<Fp; also r=beta/d<1 contradicts its r>1. For p=-d, the difference between Fp and (A+Br)/2 has quadratic coefficient -1/8-5d/408<0, contradicting Thm4.2's necessary lower sandwich. These are rigorous local obstructions, not numerical tests, and rule out these specific direct applications only.

## Stolarsky/atan comparisons examined

Read actual Chen, *The monotonicity of the ratio between Stolarsky means*, Theorem 1 and integral proof, pp2–3, [primary manuscript PDF](https://rgmia.org/papers/v11n4/Gini-and-E-mean-Ratio.pdf), newly saved SHA256 `6eb0988b1b4a34fffe9b788e8cf8db98a1ef7885ce9d5e7516e58891a6b2c4c6`. It orders the ratio E(r,s;a,b)/E(r,s;c,d) in parameters r,s according to the input ratios. A direct parameter substitution would need M itself to be a Stolarsky mean. It is not: matching quadratic and quartic centered-log coefficients forces r+s=5 and rs=2, hence {r,s}={alpha,beta}; their sixth coefficient is 437/567, while M's is 287/405, a difference 176/2835. The formulas also cover coincident/zero parameters by continuity. This rules out identity-based substitution, not every possible indirect sandwich or strong-order argument.

Read the saved Jovanovic–Treml reciprocal-arctan PDF, actual Theorem 2.1 and its proof pp106–108 (SHA256 `f21baf5cd3dc6a587292d7fe3f1b6a7a2c908360df39540db911bb05371bee4b`). Complete/logarithmic complete monotonicity of reciprocal atan alone does not compare its logarithmic derivative with this particular coth combination. Extraction of equation (2.5) has a plus sign which conflicts with g(1)=2/pi<1 and the displayed positive integrand; no formula or conclusion from that integral is used here. No new screenshot route was attempted. A prospective strong-order comparison paper was located through search but its Citeseer download returned 404; body coverage is not claimed. Yang 2009's DOI route was inaccessible; its abstract/search result is not used as a subsumption theorem. The newly retrieved 2016 characterization article (1150-9), actual Thm4.4 proof, constructs an intrinsic function for a monotone homogeneous mean; it supplies no such ratio comparison by itself.

## Current screen, chronology and limits

Fresh unauthenticated public GitHub HTML requests at 2026-10-29 06:54:49 UTC expose currentOid: OpenAI `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, count-ex-machina `dbf673741a54c7dc9d88a6aec0e8148a538f4a3a`, omega dev `5517865965160e8d20e4122aafe4e6c468c6c41d`. No rate-limited GitHub API was retried. OpenAI/count heads equal the dated 04:39 receipts; their complete dated trees were hash-verified and copied, and count registry was fetched freshly by immutable hash. Searches of these bounded indices find no target identifier/author/arctan match. Path absence is not full-text absence.

Omega's fresh Problems page reports 1538 entries but exposes only 1000 directory entries; its current D5 page exposes five category directories, not recursive contents. Thus the old complete omega trees remain explicitly dated evidence and cannot clear today's head. The live Stolarsky filename hit was read at immutable head: Bhatia–Jain mean-matrix inertia/CND, not M2 or the nested conjecture. No exclusion is inferred from title similarity. No chronology-based duplicate verdict is made for that unrelated record.

Fresh public searches used the source identifier, author pair, Conj4.7, sqrt17, atan/logarithmic/Stolarsky and proof/solution terms. FER author listing is current primary metadata; it lists the target article without a located follow-up resolution. No same-object full resolution was located. MathDB's inherited 403 route was not retried; current solution bodies are unread. This is a bounded search with unresolved coverage, not novelty certification. The 2024 preprint chronology and 2026 journal metadata do not establish whether the journal retained the question.

## Strongest objection and falsifiers

Strongest source objection: the journal may change, solve or remove the conjecture; metadata cannot settle that. Falsifier of arXiv-to-journal survival: an authenticated actual journal/accepted body whose definitions or target differ materially or already contain a resolution.

Strongest substantive objection: an older strong-order theorem may apply to S/M after a non-obvious representation. A decisive exclusion must name its actual theorem, verify every hypothesis and derive k'>0 (or the literal resultant inequality) on all t>0 for the required branches. Merely invoking elementary calculus, stabilization, M<S, parameter monotonicity or reciprocal-atan monotonicity is insufficient. A complete such bridge or pre-existing public proof falsifies the provisional non-exclusion here.

A t>0 with k'(t)<=0 falsifies the candidate's stronger derivative lemma (not necessarily its weaker resultant inequality). Positive distinct a,b with M>=R falsify the actual strict conjecture. Numerical searches could discover a witness but do not prove the universal assertion. This lane did not run numerical diagnostics. The independent exact checker is limited to algebra, local obstructions and nonidentity evidence; full finite/tail and formal gates remain open here.
