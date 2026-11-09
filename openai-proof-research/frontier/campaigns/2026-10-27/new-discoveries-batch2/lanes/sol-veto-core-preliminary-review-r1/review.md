# Independent preliminary review: rank-score veto-core distortion

Review date: 2026-10-30 UTC. Solo review; no children. Root alone adjudicates,
accepts, counts and stages. Administrative snapshot: 9 additional / 39 total,
next 40. No acceptance, Lean work, manuscript, shared edit or external posting.

**Disposition:** SOURCE PASS; ordinary MATH PASS. SUBSTANTIVE: recommend
exclusion under the campaign's routine source-proof adaptation rule, with the
complete applicable bridge below (not merely because the proof is short).
NOVELTY: bounded HOLD, not a claim of an already-published identical theorem.
FORMAL-FEASIBILITY: plausible finite proof, unimplemented and uncertified.
Root may disagree with the substantive recommendation; it is independent advice.

## SOURCE

The frozen candidate is `frozen/PROOF.md`. Rossi, *Regularizing the Veto Core*,
arXiv:2610.26535v1, Definitions 1–2 on printed p7, defines nonnegative rational
nonincreasing scores with s1=1 and q(c)=score(c)/(n S), S=sum s. Section 2.1
on p5 explicitly permits strict rankings with arbitrary distance tie breaking;
footnote 3 on p5 calls the distance a pseudometric. Section 2.2, Lemma 1,
and Section 2.3, Proposition 3, provide the fractional matching characterization.
I read these bodies, the complete Lemmas 4–5 proofs, and the actual unnumbered
conjecture after Lemma 5 on p9. It asks that the lower bound be tight, and that
the final-position score not affect distortion. The literal requested endpoint
is the universal upper bound 1+2(S-sm), every finite profile and every core
member, not a selected winner or a restricted metric class.

Rossi Lemma 5 already publishes the matching two-location sharp lower bound.
It receives no new credit here. The candidate's lower-bound restatement is
correct: n2/n1=T=S-sm, and rationality makes exact finite electorates possible.
For real scores the upper bound remains valid, with sharp supremum obtained
by rational approximation of n2/n1 from below. The review needs only rational
scores and does not add a separate extension claim. m=1 is trivial; below m>=2.

The version-pinned live PDFs retrieved during review are byte-identical to the
frozen source PDFs. Independent pdftotext extraction is also byte-identical to
the frozen text for both Rossi and Berger. Exact URLs, UTCs and response body
hashes are in `http.jsonl`; extraction evidence is in `extraction-results.json`.

## MATH: the root observation is correct

Fix a core member a and comparison candidate b. If a=b the claim is immediate.
Otherwise let W(i,c) be a witnessing nonnegative matching with row sums 1/n,
column sums q(c), and support a weakly preferred to c. Let F be the voters
whose favorite is b, p=|F|/n, q=q(b), v=sm, mu=1/S and T=S-v. For i in F,
strict rankings and a!=b imply a is not weakly preferred to b. Consequently
W(i,b)=0, and the total capacity of rows outside F gives

    q <= 1-p.

Every first-place vote for b contributes 1 and every other vote contributes
at least v. Thus S q >= p+v(1-p). Combining these inequalities gives

    (T+1)p <= T.

The original proof's high-p branch can therefore occur only at its boundary.
In particular max(0,q+p-1)=0 on every actual instance. The retained H and the
intersection estimate (6) are not essential. The assertion in the candidate
that the intersection bound is essential, and the corresponding claimed new
step in its priority discussion, are wrong explanatory claims. They do not
invalidate its inequalities or its proof of the endpoint.

### Complete simplified proof, including the classical adaptation

For c!=b split its matching column using the following good arc to each
voter j with favorite c:

    G(i,j)=W(i,c) mu/(n q(c)).

Zero q(c) columns have no incoming mass or favorite voters and are omitted.
Indeed q(c)>=mu plu(c)/n. Keep all W(i,b) as special arcs; leave the rest bad.
For each j outside F the good column sum is mu/n. Hence good mass is
mu(1-p), special mass is q, and bad mass is 1-K, where

    K=mu(1-p)+q <=1.

This is an actual nonnegative partition of W, not an assumed independent
coupling. Put r_i=d(i,b), x_i=d(i,a), D=d(a,b), R=sum r_i/n, and
E=sum(x_i-r_i)/n. On a positive good arc, a is preferred to f(j), giving

    x_i <= d(i,f(j)) <= r_i+d(b,f(j)) <= r_i+2r_j,
    D <= x_i+r_i <= 2(r_i+r_j).

On special arcs x_i<=r_i and D<=2r_i. On bad arcs x_i-r_i<=D.
Thus, retaining only upper bounds and row capacities,

    E <= 2mu R+(1-K)D,
    KD <= 2(1+mu)R.                         (*)

For the second inequality sum D/2 over good and special arcs. The source-side
r_i contribution is at most R and the destination-side good contribution is
mu sum_(j outside F) r_j/n <=mu R. No assumption on an optimal b is needed.

The score floor and the already proved p bound yield

    (T+1)K-(1+mu)
      >= v[T-(T+1)p]/S >=0.                 (**)

In particular K>0 since mu>0. Because 1-K>=0, (*) gives

    E <= [2mu+2(1-K)(1+mu)/K] R
       = 2[(1+mu)/K-1] R <=2T R,

where the last step is (**). Multiplying by n proves
SC(a)<=(1+2T)SC(b) for every b. No division by R, D or SC(b) occurs.
If R=0, (*) forces D=0 and E<=0; hence SC(a)=0. If D=0, the triangle
inequality in both directions gives x_i=r_i. Zero scores, zero plurality,
zero distances, n=1, tied distances and pseudometrics all remain covered.

### Original argument separately checked

The candidate's finer bounds are also correct: E<=2mu(R-H)+(1-K)D and
KD/2<=(1+mu)R-mu H, with H=sum_(i in F)r_i/n. Its intersection lower
bound is valid but only says H>=0 on actual instances. Its scalar certificate
even holds on the stated relaxed domain: in the second branch q>=1/(T+1),
so q+p>=1 and K+mu(q+p-1)=(1+mu)q. Its displayed (8) follows by multiplying
the lower bound on R by T-mu>=0. At T=mu=1 the multiplier is zero, with no
division by that difference. Thus redundancy is not a mathematical failure.

## SUBSTANTIVE: actual closest body and complete adaptation

Berger–Feldman–Gkatzelis–Tan, *Learning-Augmented Metric Distortion via (p,q)-Veto
Core*, arXiv:2307.07495v3, Section 3.1 printed pp7–12, is the closest body.
I read Definition 3.5; the full Lemma 3.6 construction and equations (2)–(3);
Corollary 3.7; Observation 3.8; full Lemmas 3.9–3.10; the full proof of
Theorem 3.4; and the general-weight statements in Section 3.2.

Theorem 3.4 states only 1+2/mu with mu=min n q(c)/plu(c). Rossi Lemma 4
substitutes mu>=1/S, producing 1+2S. Neither that theorem nor Corollary 3.12
states the complete distinguished-column coupling needed here. Theorem 3.13
is tight in its discrepancy parameters, not tight within the rank-score family.
It cannot be quoted as a subsumer of Rossi's sharper conjecture.

The complete routine-adaptation objection is more specific:

1. Use Berger Lemma 3.6 equation (2) with any valid plurality floor mu=1/S,
   but only for favorites c!=b. Keep the entire original b column separately.
   The same column-sum calculation gives mu/n outside F. This is exactly the
   decomposition used above. Its bad mass changes from 1-mu to 1-K.
2. Berger Observation 3.8 and Lemma 3.9 give precisely the good-arc excess
   and separation estimates above (with arbitrary comparison b replacing c*).
   On the retained column consistency itself gives excess<=0 and D<=2r_i.
3. Repeat the sum in Berger Lemma 3.10, keeping that column instead of
   discarding it with the dummy vertex. Total useful mass is K and the
   two voter contributions remain bounded by (1+mu)R. This is the second (*).
   Repeat the sum in the proof of Theorem 3.4 for the first (*).
4. Matching support supplies q+p<=1. The literal source score floor supplies
   p<=(S-v)/(S-v+1) and (**). Substitute into (*) exactly as above.

This exhibits the entire applicable classical/source proof bridge for every
score vector, profile, core member and pseudometric. It leaves no analytic,
asymptotic or optimization assertion to numerical inference. The modifications
are a distinguished-column retention in an existing fractional matching sum
and the immediate score/capacity inequalities. Under this campaign's express
exclusion of routine proof adaptations, I recommend no substantive credit.
That is a judgment about this complete adaptation, not a claim that the older
paper explicitly proved Rossi's conjecture, and not an argument from length.
The independent ordinary resolution and its stronger column bound remain
mathematically useful and should be preserved even if uncounted.

## NOVELTY and access limits

Rossi v1 was submitted 2026-10-19 14:58:48 UTC. Berger v1 was submitted
2023-07-14 17:28:24 UTC; v2 2024-07-08 17:53:55 UTC; v3 2024-07-11
17:57:47 UTC. These precede this review. The arXiv versions, not separately
authenticated publisher versions, are compared. Exact pinned URLs are
https://arxiv.org/pdf/2610.26535v1 and https://arxiv.org/pdf/2307.07495v3.

No independent broad scouting was requested or performed. The frozen earlier
lane's current arXiv search and historical screening are bounded evidence,
not a current registry clearance by this reviewer. Its failed quoted-title
request was HTTP400, not a clean no-results search (the earlier scout prose
is imprecise here). GitHub API/raw/codeload/diff/patch and ScienceDirect/Google
challenge routes remain denied; none was retried. No proxies or bypasses.
The review made only four successful version-pinned arXiv requests. No
MathSciNet/zbMATH, exhaustive citing-body coverage, current registry head
or full historical clearance is claimed. Parked intervals remain parked.

## FORMAL-FEASIBILITY and independent evidence

The simplified argument uses finite weighted sums, support, triangle
inequalities and elementary ordered-field inequalities. A literal formal
endpoint would still need a finite strict-ranking model, consistency bridge,
core-to-matching dependency and zero-column-safe split; none is certified
here. Feasibility is favorable, but no Lean or manuscript investment was made.

`check.py` independently implements exact rational augmenting-path flow and
arc checks, rather than reusing the candidate's checker. It checks 17,472
feasible rational scalar cases and 4,921 comparison pairs among 1,900 core
members in 1,600 generated finite line-pseudometric instances, including 26
zero-R and 640 zero-D comparisons. All final assertions pass. The first
checker run failed because its relaxed scalar generator allowed K>1; the
failed source and diagnostic are retained. This was a checker-domain bug,
not a proof counterexample. Finite line checks are not a proof of full scope;
the complete proof is the preceding symbolic argument.

## Integrity and procedural qualifications

`input-bindings.json` binds assigned scientific original files and frozen
copies. Administrative ledger, prior context, AGENTS and NEXT are snapshots
only and are not bound against mutable originals. Before/after scientific
hash checks and final independent manifest verification are separate files.
The manifest explicitly excludes itself and its verification receipt.

Two initial read-only operations preceded freezing: an overbroad unguarded
rg discovery (output truncated), and a guarded display of candidate/source
metadata and PROOF. This did not meet the requested all-retrieval-under-guard
and freeze-before-work order; the exception is disclosed rather than erased.
All subsequent helper, retrieval, extraction, hash and checker commands used
the specified guard and environment with unchanged AS/RSS512MiB, CPU210s,
wall230s caps. Native bounded instruction reads and apply_patch were used.
No git, browser, shared writes, external messages/posts/uploads or MathDB edits.
