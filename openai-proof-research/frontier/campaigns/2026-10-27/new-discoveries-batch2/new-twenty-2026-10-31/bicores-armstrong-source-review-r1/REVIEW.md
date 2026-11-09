# Independent review of MathDB 336969

Recommendation to root: EXCLUDE FROM SIGNIFICANT-DISCOVERY CREDIT as a complete routine adaptation of earlier quadratic cyclic averaging to the product parametrization already proved in the target source. The ordinary all-parameter proof is sound with indexing clarified below. This is a significance recommendation, NOT a claim that Johnson or Wang printed this bipartition theorem, and NOT acceptance. Credit remains 0; campaign 52/60 beyond 39 unchanged. No formal execution or Pi dispatch.

## Separate gates

* Literal binding: PASS. The raw parsed statement hashes to d7611729af5795242c529dea59c665fe959bc89bc33b4b4a4fa33e3fc675154e; exact source Conjecture 4.6. All positive s, 0<=a,b<s, gcd(s,a-b)=1, unweighted total size of BOTH partitions.
* Source conventions and ordinary mathematics: PASS relative to the stated primary-source dependencies, with a source indexing slip repaired explicitly. No computation or upstream-truth audit.
* Accepted-version comparison: PASS for the inspected statements, normalization and construction in the author copy against arXiv v2. Final published-version/corrections gate: INCOMPLETE. Exact final page returned 403; it was not retried. This gap would need resolution before positive qualification; it is not my basis for significance exclusion.
* Prior: bounded nonidentification of a later exact proof, not absence clearance. Johnson/Wang comparison is complete for the named mechanisms and hypotheses. They do not directly subsume the literal target as printed.
* Literature novelty: NOT ESTABLISHED. A conjecture label and unsuccessful searches do not establish novelty.
* Significance: recommend FAIL under the campaign's routine-adaptation exclusion, with the entire adaptation and strongest objections below.
* Formal feasibility: plausible but substantial partition/beta-set infrastructure; no Lean endpoint, dependency audit or replay exists. Formal gate UNMET.
* Acceptance: ROOT ONLY; not requested or granted here.

## Independent ordinary proof and obligation audit

For s>1 write d=b-a and c=(s-1)/2. Subscripts are in Z/sZ, but d,a,b in affine increments denote their actual integers. Let Omega be the product of the binary length-s vectors U of weight a and V of weight b. It is finite and nonempty, even when one weight is zero. Full weight s is outside the target; the fixed-weight moment and stabilizer arguments also handle a constant full vector if encountered in the auxiliary reasoning.

The source defines a beta-set B(lambda)={lambda_j-j:j>=1}; an s-set entry is the SMALLEST absent integer of a residue, not its largest bead. Thus the runner with first hole z_i consists of i+s k for k<q_i when z_i=i+s q_i. Fayers Proposition 2.5 gives the s-core closure characterization, and Proposition 4.4 gives exactly
 y_i=x_(i+a)-a+s U_i=x_(i+b)-b+s V_i.                 (1)
No shift in the beta convention is harmless without changing this equation. For a>0, Proposition 2.7 has e=s-a for charges (0,a). Shifting its inclusions by a yields B(lambda) subset B_a(mu) subset B_s(lambda); thresholds consequently give x_(i+a)<=y_i+a<=x_(i+a)+s, in multiples of s. For a=0, its inclusions and charge-zero equality force equal beta-sets, hence x=y and U=0. This agrees with (1). Lemma 2.3 supplies both s-core components. This validates the use of Proposition 4.4 from the actual beta conventions, rather than merely borrowing a count.

Subtract the two equations in (1), setting j=i+a:
 x_(j+d)-x_j=d+s(U_(j-a)-V_(j-a)).                  (2)
Because d generates the residue cycle, this specifies integral x once x_0 is fixed. The sum of all increments is sd+s(a-b)=0, so it closes. It is unique up to one common integer translation; y then follows from (1). Modulo s, x_i=i+C, and y_i=i+C as well. The sum of a complete residue system is s(s-1)/2 modulo s, even for even s; hence a UNIQUE INTEGER common translation makes sum x_i=s(s-1)/2. Summing (1) gives the identical sum for y. The step uses the congruence of the sum, not a false division in Z/sZ.

After normalization choose C in Z/sZ with x_i congruent i+C, and define z_j=x_(j-C), w_j=y_(j-C). These are correctly indexed normalized s-sets. In particular z_j congruent j and sum z_j=s(s-1)/2. Set q_j=(z_j-j)/s. Then sum q_j=0. The associated runner union B is bounded above, has cofinite negative tail, and has charge sum q_j=0. Order it decreasingly as beta_1>beta_2>... . Zero charge means beta_j=-j eventually. Consequently lambda_j=beta_j+j is eventually zero, nonincreasing (successive beta differences are at least one), and nonnegative. It is a finite partition. Closure of B under subtraction by s proves it is an s-core. This proves reconstruction including negative runner charges; the same applies to w and mu. Equation (1), reindexed by j-C, proves membership in both bicore classes by Proposition 4.4. Conversely every class member has normalized s-sets and unique binary coordinates in (1), of weights a,b by summing the equations. Thus no extra rational or charged objects enter the class.

Indexing repair in the source: arXiv text 1031-1035 / accepted text 999-1005 say diamond_i=x_(i-k), then display the corresponding difference as g u_(i+k). Direct substitution into (*) gives g u_(i-k). Use that latter subscript (or reverse the definition of the shift parameter). The claimed orbit and count are unchanged. The author's candidate uses a common relabeling and does not need the erroneous displayed sign; here the relabeling is made unambiguous as z_j=x_(j-C). This is a repair of the source derivation, not a new mathematical result.

Uniformity cannot be inferred from a count alone. If T_h U has coordinates U_(i+h), the normalized solution is x'_i=x_(i+h), y'_i=y_(i+h), so C'=C+h and z',w' equal z,w. Conversely two solutions for the same pair have x_i=z_(i+C), y_i=w_(i+C); changing C gives exactly a simultaneous cyclic shift of U,V. Fibers are therefore precisely cyclic orbits. If a shift of order t>1 fixes both vectors, each orbit on the index set has t entries, so t divides a and b as well as s. It then divides b-a, contradicting gcd(s,d)=1. This argument requires neither gcd(s,a)=1 nor gcd(s,b)=1. Individual vectors may have shorter periods; their COMMON stabilizer is trivial. Every fiber has exactly s elements. Uniform independent U,V consequently pushes forward to the UNWEIGHTED arithmetic measure on the finite nonempty class, of size binom(s,a)binom(s,b)/s. Empty weights cause no exception. Repeated index orbits are fully covered by the divisibility argument.

For a normalized s-set, the signed runner contribution to size is
 i q_i+s q_i(q_i-1)/2.
For positive q this is the sum of added beta numbers; for negative q it is minus the sum for k=q_i,...,-1 of i+s k. Both give the same polynomial. To justify the beta-number size formula, truncate B and the empty beta-set below one sufficiently negative cutoff. Charge zero makes the retained lengths equal; summing lambda_j=beta_j+j cancels the common j terms. Hence
 |lambda|=(sum z_i^2-sum i^2)/(2s)
          =sum (z_i-c)^2/(2s)-(s^2-1)/24.             (3)
No absolute value or nonnegative-charge hypothesis is implicit. This is exactly Wang Lemma 4.10 in Fayers' first-hole coordinates. Relabeling leaves all sums of squares invariant.

Put A=a(s-a), B=b(s-b), W=A+B. Uniform weight-a sampling gives E U_i=a/s and E U_i U_j=a(a-1)/(s(s-1)) for distinct i,j. Thus Var U_i=A/s^2 and Cov(U_i,U_j)=-A/(s^2(s-1)); these also hold when a=0. The corresponding formulas for V replace A by B. Product sampling makes every mixed U,V covariance zero. The increments Delta_j on the right of (2) therefore satisfy
 E Delta_j=0, E Delta_j^2=W,
 E Delta_j Delta_k=-W/(s-1) (j!=k).
For an l-edge segment of the d-cycle, the edges are distinct for 1<=l<=s-1, so
 E (x_(j+ld)-x_j)^2=W l(s-l)/(s-1).                (4)
The deterministic d disappears because d+s(a/s-b/s)=0; forgetting it before centering would be wrong.

For any vector of mean c,
 sum(x_j-c)^2=(1/(2s))sum_(j,k)(x_j-x_k)^2.
There are exactly s ordered pairs of each nonzero d-cycle distance l. Using (4) and sum_(l=1)^(s-1) l(s-l)=s(s^2-1)/6 gives
 E sum(x_j-c)^2=W s(s+1)/12.                       (5)
The ordered-pair factor is 1/(2s), not 1/s. This pays both the variance constant and the even-s case.

For the SECOND component, compute directly from (1) and (2):
 y_(i+d)-y_i
 =x_(i+b)-x_(i+a)+s(U_(i+d)-U_i)
 =d+s(U_(i+d)-V_i).                               (6)
Here (U_(i+d)) is still a uniform weight-a vector independent of V. Its entire off-diagonal covariance table is unchanged. The same distinct-edge calculation and pairwise identity prove (5) for y. There is no assertion that x and y are independent, and none is needed. In fact the two marginal expectations each equal (s+1)(W+1-s)/24, though the individual bipartitions need not have equal component sizes.

Apply (3) to BOTH components and (5) to each. Their total mean is
 (s+1)W/12-(s^2-1)/12=(s+1)(W+1-s)/12,
exactly the literal target for every allowed s>1,a,b.

For s=1, a=b=0 and gcd(1,0)=1. Fayers' explicit convention gives only the empty bipartition and zero mean, matching the formula. Unlike the single-partition content-uniqueness issue, the source says this convention IS consistent with the multipartition definition for l>=2. The candidate's suggestion of a possible content-convention discrepancy at this bipartition endpoint is unnecessary. There is no unpaid s=1 semantic bridge here.

## Complete earlier-result-to-target comparison and significance adjudication

Johnson 1502.07934v2, Theorem 3.7 proof and Corollary 3.8 (810-869), treats ONE simplex for ordinary coprime cores. The quadratic degree argument uses Ehrhart/Euler-Maclaurin reciprocity and three special values. It does not assert polynomiality for the present product of hypersimplices or handle these two charges. Taking a=0 gives twice the ordinary (b,s-b)-core mean, but cannot prove the general case. So Johnson's printed theorem is a concrete NONMATCH, not a direct subsumption.

Wang EJC23(1)(2016)#P1.4 Theorems 1.1-1.4 (105-151) distinguish ordinary unweighted, self-conjugate, and stabilizer-weighted averages. None has the literal bipartition class. Proposition 4.7 (630-649) moves a cyclic quadratic statistic from a charge-constrained simplex to all weak compositions through equal cyclic fibers. Lemma 4.10 (770-887), including its discrete-calculus proof, is EXACTLY (3); its proof explicitly includes negative contributions. The proof of Theorem 1.1 (895-930) substitutes single-coordinate and two-coordinate moments into that quadratic. The weighted Theorems 1.3/1.4 cannot replace this target's unweighted measure.

Here is the full adaptation, without silently changing the measure or restricting parameters. Replace Wang's one weak-composition sampling space by Omega, already identified with bicore orbits in Fayers' Theorem 4.2 proof (995-1043). Use the common-stabilizer argument above to supply equal fibers; this is the same cyclic-averaging principle as Proposition 4.7, now on a product. There is no requirement that each factor have a free cyclic action. Replace the weak-composition first/two-point moments by the displayed fixed-weight binary moments. Use Wang's first-hole size identity separately on each component. The linear transport in Fayers' (*) has first marginal increment (2) and second marginal increment (6). In each, the two independent centered fixed-weight vectors contribute additively to the variance, giving W; the relative index shift is a permutation preserving their moments. Evaluate the same cyclic quadratic through pairwise differences, equations (4)-(5); subtract the TWO constants in Lemma 4.10. This yields the target formula above. All steps of this adaptation, including partition reconstruction, uniformity and both transports, have been supplied rather than deferred to an unproved product lemma.

Why I recommend exclusion: the nontrivial object parametrization is already in the original source's Theorem 4.2 proof, not a newly invented bijection. The exact size functional and the cyclic-quotient quadratic-moment computation were already explicit in Wang. After these old results, the change in sampling domain needs only the elementary two-point inclusion probability for a uniform subset; product independence adds the two variance coefficients. The second marginal is a shifted copy of the same computation. This is a complete routine extension of that published mechanism to the source's published parametrization. I am not inferring insignificance from shortness, tools being standard, or a=0. The full general bridge is what makes the exclusion recommendation defensible.

Strongest objections to this recommendation: Fayers states this precise general formula as a conjecture AFTER Johnson and Wang and explicitly hopes to extend geometric methods. Thus those papers plainly do not themselves advertise this deduction, and the product-uniformity and second marginal are real obligations that could be overlooked. Discovering the right variance organization may have scholarly value and could merit publication independently of this campaign. Also 'routine' is a substantive judgment, not a logical consequence of the proof's validity. Root could reasonably disagree about the threshold. My response is that the published Fayers proof already exposes the required product and affine transport; no new structural classification, new source theorem, or non-elementary moment identity is needed once the full displayed substitutions are performed. This supports the campaign exclusion while leaving any first-in-literature claim unresolved. Do not label this 'known theorem proved by Wang'.

## Source finality, bounded public investigation and chronology

arXiv v2 is dated 3 July 2018; first submission 31 August 2017. The cached accepted author PDF identifies European J. Combin. 76 (2019) 138-158 but its header DOI 10.1112/plms.12087 conflicts. The actual author index associates this exact title/pages with 10.1016/j.ejc.2018.09.012. That DOI resolves to Elsevier PII S0195669818301719, whose HTML names the exact title. This authenticates the citation and accepted-copy routing, not the entire final body. The final ScienceDirect article GET returned 403. No retry, alternate endpoint, correction-body access, or barrier bypass was attempted. The accepted copy's Theorem 4.2 construction, Proposition 4.4 and Conjecture 4.6 agree in relevant mathematical content with arXiv v2, including the relabeling slip discussed above. Exact final-body comparison remains an identified gap. Two targeted search batches found no concrete correction or later exact resolution; this is bounded nonidentification, not a claim of no corrections or no proofs worldwide.

Johnson 2015 and Wang 2016 precede the source and this review. No new matching public theorem body was identified that would require a priority/scope comparison beyond those actual bodies. Search snippets for weighted ordinary cores do not imply a later bipartition proof.

Current registry roots were read sequentially on 2026-11-07 UTC, with exact times/URLs/hashes in public-access.json. Heads: openai/math 4eaee87548250b2682affda7d05d947c05554bae; LeanPool/lean-pool 364b613903fd76bc2b385eda32507a2650e84dcd; TauCeti ea3c28f71e69f5bfb5c214037cc08606032ff30a; formal-conjectures 2055e5adadae0b2e392365938faa82ef6f1464f0. The completed comparison seed had TauCeti e7068108eef137a393590a3e2a09f9b2dbb8b9e4 at 06:17; this later different observation proves no ancestry or rollback. The frozen openai routing pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (8 October 2026), not the current head.

I read current pinned openai CONTENTS and the literal pinned LeanPool.lean/TauCeti.lean root imports, plus formal-conjectures PROOFS policy. Neither root import is a complete mathematical inventory. The pinned local preprints-tree is the path inventory; tree.json was not used. No matching target text appeared in the bounded catalogue checks, and no matching proof body was identified. These observations do not clear full trees, concealed/transitive imports, external proof links or unindexed literature. A statement in formal-conjectures is not automatically a proved theorem. Search/API/build claims were not substituted for proof-body examination.

## Formal feasibility and stopping decision

An eventual literal certificate would require source-defined partitions and content uniqueness, the beta-set core criterion and reconstruction, normalized s-sets, free quotient and uniform averaging, signed size identity, fixed-weight rational moments, and BOTH increment transports, ending in finiteness/nonemptiness and total-size sum = cardinality times the formula, with s=1 included. These are substantial formal bridges; no coordinate-only theorem suffices. No API exploration, Lean, mathematical program, solver or replay was run. Because I recommend campaign exclusion, no dormant Pi implementation brief is written or dispatched. If root overrides the significance judgment, final-body/source clearance and the entire formal pipeline remain unpaid; this review itself confers no prospective acceptance.

## Operational integrity and limitations

The prescribed bootstrap and frozen-before were the first and second commands exactly. All subsequent substantive disk/public GET reads used the supplied run.py with unique receipts; text and public response writes used write_lane.py. Frozen-after and manifest verification complete the handback. The resource inventory contains the actual sampled values and exits; a fast process can escape RSS sampling, group sampling is not a cgroup guarantee, and cumulative child CPU is not aggregate CPU enforcement. Search-service resource telemetry is unavailable. The supplied writer and bootstrap/verifier have narrower self caps as documented. There were no mathematical programs, formal execution, children/delegates, git, browser/preview, shared writes or protected body inspections.

Two candid scope/output exceptions: initial_reads used a wrong top-level lookup on raw-provenance.json (the target is inside records), causing it to PRINT unrelated raw record metadata from that authorized container; it did not follow their paths or read other source bodies. Subsequent scoped_sources_one selected records.336969 correctly. Some early console extracts were truncated; complete receipt output is preserved, and focused subsequent reads supplied the theorem passages actually used. registry_seeds likewise exceeded console output limits; only its visible roots and focused metadata are relied on. This is not described as perfect target-only initial output discipline. The TASK explicitly required BRIEF/CANDIDATE/ORDINARY-ROUTES in full; reading those required author files did not authorize following unrelated proof paths, and none were followed.

The native web search calls are a documented exception to run.py execution: they cannot be run inside that local runner. Their session results and contemporaneous following runner summaries are preserved, without retroactive service-telemetry claims. No independent GET from web.open was used. Eleven explicit direct GET attempts were made; counting the DOI's automatic linkinghub redirect conservatively gives twelve distinct requested resources. Two search batches, below three. All activity has settled; no jobs left running. Root alone adjudicates. Zero credit; 52/60 unchanged.
