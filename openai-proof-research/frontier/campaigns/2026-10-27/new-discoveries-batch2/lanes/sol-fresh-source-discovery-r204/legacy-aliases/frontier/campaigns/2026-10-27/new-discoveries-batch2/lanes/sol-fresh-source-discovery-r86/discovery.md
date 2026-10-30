# r86 source-first discovery screen — zero eligible outcomes

Disposition: credit 0. No nomination for Lean, paper, acceptance, or counts. This lane screened three candidates and pursued the best attributable one through its complete elementary reduction. The reduction is excluded under the explicit rule against routine derivatives/formula specialization. No PROOF.md is created for a nominated substantive result.

## Governing context and duplicate gate

Read ancestor openai-proof-research/AGENTS.md, batch AGENTS.md, NEXT.md, ledger.json, prior-campaign-context.json, immutable upstream.json, and catalogue introduction. Current continuation is 8 additional / 38 total; historical ledger entries do not supersede it. Read r84 provenance and raw compare evidence, the root registry inventory description, and actual root lasso and silicosis exclusion bodies. Those bodies reinforce two distinct requirements: exact source quantifiers and a mechanism beyond elementary specialization. No excluded family was reopened, and no work on the active DeWitt–Keith or r85 targets was performed.

Initial rg -l across all project dates, including FINDINGS, discovery, SUMMARY, provenance, ledgers, context, and NEXT, found no reports mentioning the three target names/identifiers. The later saved all-date filename-first pass and bounded-section pass are in all-date-report-filenames.txt and all-date-report-sections.json. This negative textual result is only a duplicate diagnostic, never priority clearance. Root lasso and silicosis exclusion bodies are included in the latter file as relevant method comparisons. An additional method-report filename inventory is retained. The assigned lane is excluded from its own duplicate screen.

## Candidate 1: Eruguz et al., published Conjecture A.1

Primary: Ayse Sena Eruguz, Oktay Karabağ, Eline Tetteroo, Carl van Heijst, Wilco van den Heuvel, Rommert Dekker, *Customer-to-customer returns logistics: Can it mitigate the negative impact of online returns?*, Omega 128 (2024), 103127, DOI 10.1016/j.omega.2024.103127. Retrieved the actual publisher PDF from the Erasmus institutional repository, whose cover identifies it as the Version of Record. The conjecture is on printed p16, not an inferred abstract interpretation. Section 4.1.3 explicitly says the authors are unable to prove worst-case unimodality. Read §§4.1.1–4.1.3, equations (1)–(3), Assumptions 1–2, definitions of phi_B/phi_W, and Appendix A through Theorem A.1 and the conjecture. Source extraction retained locally.

Exact target: unimodality of E[Pi_W(a)] on 0<=a<=1 in the linear purchase-probability base model. Assumption 2 is q(a)=q0+a(1-q0), 0<=q0<1; T=T^M is a positive integer. The appendix separately restricts its worst-case optimization characterization to T!=1. The reduction below covers T=1 as well, without claiming extra credit. Use Assumption 1 for the conventional-profit identity (A.2). Source parameters give s=p^C2C>=0, K=P(1-p^FR)>0, C=E[Pi], phi=phi_W=phi_B+C. No assumption phi>=0 is imposed. All underlying cost/probability restrictions may be retained because the argument works for every real phi.

Before deriving the reduction, retrieved and read Boyd–Vandenberghe's actual convex-optimization slides, scalar and general composition rules, slides 3.24–3.25. They give the differentiable composition formula and curvature/monotonicity conditions; concave-increasing composition follows by negation. The map u/(1+su) is increasing concave for u>=0, s>=0. This is a classical mechanism comparison, not an assertion that their text states this retail conjecture. The published source's own Appendix A is the closest same-object body and was read first.

### Completed elementary reduction, retained solely to justify exclusion

Set x=1-a, c=(1-q0)^T in (0,1], m(x)=1-c*x^T. Equations (2)–(3) and (A.2) give exactly

F(1-x)=C+s*m(x)*(K*x-phi)/(1+s*m(x)).

In particular, subtracting the constant C is justified; unimodality of the best-case numerator alone would not justify unimodality of an arbitrary quotient. For s=0 the objective is constant. For s>0 put b=phi/K and w=m/(1+s*m). On 0<x<1, m>0, m'<0, m''<=0, and

w'=m'/(1+s*m)^2<0,

w''=m''/(1+s*m)^2-2s*(m')^2/(1+s*m)^3<=0.

The nonconstant factor of F-C is h(x)=(x-b)w(x). Thus

h'=w+(x-b)w',   h''=2w'+(x-b)w''.

If x<b then h'>0. If x>=b then h''<0. For b>=1, h increases throughout the open interval. For b<=0, h is strictly concave throughout it. For 0<b<1, it increases up to b, has h'(b)=w(b)>0, and its derivative strictly decreases on (b,1). Consequently its derivative crosses zero at most once, from positive to negative. These cases give a nondecreasing-then-nonincreasing function on [0,1], including endpoint maximizers, by continuity and the mean value theorem. A reflection x=1-a preserves this property. For b<=0, the standard strict-concavity derivative criterion gives the same property even if the maximizer is an endpoint. All endpoint cases follow by continuity; no change to the intended model or endpoint-domain correction is used.

The checker independently differentiates the quotient numerator/denominator at rational points and verifies both identities and their two sign regions in 16,416 cases (T1–16, three q0 values, three s values, nineteen x values, six b values). This checks transcription and finite arithmetic only; the universal argument is above.

Disposition: EXCLUDE_ROUTINE, no discovery credit. This is precisely a formula substitution plus a second-derivative sign split. The source authors' open statement does not override the campaign's substantive standard. No exact earlier printed solution is asserted.

Strongest objection to exclusion: the complete statement apparently remains unproved in the source, and the negative-gain region requires care. Answer: h'>0 on that entire region is a one-line consequence of the same explicit derivative; there is no remaining uniform parameter inequality. Reopening falsifier: a source-faithful wider model with genuinely nonlinear q outside Assumption 2, or a substantive residual inequality not discharged by this calculation. Such a broader attributed conjecture was not obtained. The present proof cannot be advertised as a result for arbitrary increasing q.

## Candidate 2: Hyman, persistence density

Primary: James M. Hyman, *Why Eight Percent of Benford Sequences Never Converge*, arXiv:2603.18243v1. Read Definition 3.11, Theorem 3.13, Corollary 3.16, Conjectures 3.17–3.18, and surrounding discussion in the actual PDF, not just the title or heuristic.

Conjecture 3.17 displays lim_(B->infinity) #{b<=B: b is B-EQUI-PERS}/(B-1)=1/12. But Corollary 3.16 defines B-EQUI-PERS **for sample size N** through existence of k with q_k<=N and a_(k+1)q_k>N log N. The displayed conjecture does not specify a fixed N, N(B), or an order of limits. Earlier numerical discussions use finite sample sizes, and the title's nonconvergence is not an exact universal asymptotic claim. Accordingly no guessed persistence quantifier was supplied, and no Weyl-theorem 'refutation' was manufactured. Conjecture 3.18 likewise concerns a rate with additional quadratic-scaling context; no full rate proof is supplied here.

Disposition: SOURCE_SCOPE_HOLD, unresolved, credit0. Exact gap: an attributable complete sample-size quantifier for the density claim. Strongest objection: surrounding experiment choices could imply fixed N=10000. That inference is possible, but is not a precise obtained all-B source statement. Falsifier/reopen: an explicit source clarification or later exact version fixing N and the limiting convention. No contact was made. The conditional or defective neighboring proof passages are not counted as a substantive discovery.

## Candidate 3: box fragmentation

Read the exact original primary source: Livia Betti, Irfan Durmić, Zoe McDonald, Jack B. Miller, Steven J. Miller, *Benfordness of measurements resulting from box fragmentation*, arXiv:2304.08335v1, Definition1.7, Theorem1.9, and Conjecture4.1. Original target: every continuous linear-fragmentation process with finite stated moments satisfies the maximum criterion for every 1<=d<=m. Definition1.7 also imposes independent coordinate cuts, fixed stage law, and common finite log mean and strictly positive log variance. This is a genuine full quantified target.

Closest successor actually read: Bruce Fang and Steven J. Miller, *Benford behavior resulting from stick and box fragmentation processes*, arXiv:2508.12915v1, introduction, Theorems1.10–1.13, and surrounding source comparison. It explicitly announces a result on the original conjecture, but Theorem1.13 has additional bounded-log and density/CLT approximation hypotheses; therefore its abstract alone cannot clear the original full claim as resolved. Moreover its literal hypotheses include E[log_B(P_i)]=0 with P_i in (0,1), whereas the original definition permits a negative common mean. That literal incompatibility is a source/normalization concern, not an eligible endpoint/domain correction or a proposed new counterexample. No claim is made that the intended successor theorem is false, or that the original conjecture is known resolved in full.

Disposition: PUBLIC_CLOSEST_BODY/SOURCE_HOLD; full original conjecture unresolved here, credit0. Exact gap: all-law maximum-product equidistribution with the original intended hypotheses, beyond the successor's printed additional conditions. Strongest objection to stopping: centered logarithms may be intended and a general local-limit argument might extend the result. That may be so; no full proof of that extension was established. Falsifier/reopen: actual corrected/published theorem and proof, or an independently complete all-law argument. Do not claim novelty from the zero-mean printing issue.

## Current public registries and access limits

Live unauthenticated HTTP head reads at the UTCs in http.json give Omega 6f8ee6614e0faf9dfa2cce46d1eb758dea97c335 and OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a. Consulted complete cached final-freeze inventories: Omega baseline1b999d9fda71df7537b62327147496d64a6f66ef,350197 entries, and OpenAI174524 entries. The first exploratory path screen also used the older70af inventory; it is explicitly superseded for the final baseline. The fresh raw Omega compare from1b999 to observed head reports48commits,48returned,123files (<GitHub's300-file cap); the later23a4-to-head compare is also retained. These are path-level changed-file evidence, not a complete new tree or semantic absence guarantee. No exact source-name path was found; one raw regex hit was a random hexadecimal digest and is not relevant evidence.

Actual current Omega StrongConcavityAttainment.md body was obtained and read. It concerns an abstract strongly concave function with completeness and boundedness hypotheses and explicitly claims no literature novelty. It neither states this retail model nor proves its missing shape hypotheses; it is not a same-object prior proof. No inference equates Blueprint prose with Lean validity. No registry Lean replay was done. Classic Boyd text and closest primary target/successor bodies carry the substantive screening, not filename absence.

All requested HTTP downloads succeeded with200 in this lane; no403/429/challenge retry, bypass, proxy, browser, account, contact, posting or upload occurred. Searches were bounded and do not certify worldwide priority. Sources are pinned by content hashes even when the institutional/Stanford URL itself is mutable. No journal body is silently treated as read: only candidate1's actual VoR was obtained; candidates2/3 are specified arXiv versions.

## Reproduction and handoff

Run `bash run.sh` in this lane for the capped exact arithmetic checker. helper_guard.py is byte-copied from the specified improved packet guard; it self-limits supervisor AS, caps child AS512MiB, process-group RSS512MiB, CPU210s, wall230s, uses nominal40ms sampling and sets BLAS/OpenMP threads1. No cap was raised. Sources, fetch scripts, HTTP UTC/hash records, all-date gates and file hashes are retained. No new source resolution meets the full eligibility standard. Keep counts8/38. No shared files changed.
