# r110: three primary claims screened; zero complete discoveries

Credit **0**. Campaign counts remain **8 additional / 38 total**. No PROOF.md, Lean, paper, shared edit, child, git operation, external message or publication.

## Scope and source chronology

Read ancestor and batch AGENTS, ledger, NEXT, prior-campaign-context, pinned upstream metadata and catalogue; streaming hashes are in context-read.json. Existing finite r108 and analytic/geometric r109 work was not adopted. All expressly exhausted families in the assignment remain excluded; no r104 evolution-algebra renaming was pursued.

The live arXiv abstract histories retrieved on 2026-10-29 list Kudra v2 (15 June 2026; v1 8 May) and Marashdeh v1 (12 August 2026). The initial Kudra v1 download was immediately superseded for attribution by the actual v2 body. These are latest versions advertised by the retrieved histories, not a claim of worldwide freshness. Exact HTTP times, headers, source bytes and SHA256 values are preserved in http.json and source-manifest.json.

### 1. Kudra Conjecture 1, arXiv:2605.07628v2

For every natural n, X_n=Y_n. Here X_n consists of all degree-n real polynomials g with strictly positive coefficients such that, for every m<=n and every degree-m positive-coefficient polynomial f with all roots in the open left half-plane, the coefficientwise product f*g also has all roots in that open half-plane. Define Q^(2l)=(1+x^2)^l and Q^(2l+1)=(1+x)(1+x^2)^l. Y_n consists of all such g for which, for every k>=2 and shift m>=0 with k+m<=n, (g*(x^m Q^k))/x^m is quasi-stable (all roots in the closed left half-plane).

Read v2 Introduction, Sections 2–6, Theorems 6,8,9,10 and their proof bodies. Theorem 6 already proves X_n subset Y_n; Theorems 8–9 settle n<=5. Theorem 10 already treats paired even/odd coefficients for arbitrary odd degree. None of those results is nominated as new. **Unresolved full scope.**

### 2. Kudra Conjecture 2, same v2, Section 5

For every n, X_n^star=Y_n^star. X_n^star uses nonnegative intermediate coefficients, positive leading/constant terms, and preservation of every quasi-stable input of each degree m<=n. For odd n, Y_n^star=Y_n. For n=2l it adjoins polynomials g_e(x^2), g_e positive-coefficient of degree l, for which g_e*(1+x)^nu has only negative real roots for every 2<=nu<=l. This additional even-only branch is part of the source statement and was not dropped. **Unresolved full scope.** It shares the unresolved relative-interlacing step with Claim 1; the branch already governed by finite multiplier sequences earns no credit.

### 3. Marashdeh Conjecture 4.9, arXiv:2608.12531v1

For every numerical semigroup S other than N, t(S)<=e(S)-1+sigma(S). Here F is its Frobenius number, e its minimal-generator count, PF its pseudo-Frobenius set, t=|PF|, and sigma=sum over f in PF of |S intersect (f,F]|. Read Sections 3–5, actual Conjecture 4.9 and Theorem 4.4 proof. The latter proves the analogous bound with Xi<=Theta (redundancy of the gap covering), not with sigma (dominance defect). The source's genus<=35 computation is evidence only. Source Conjecture 5.2 is explicitly at least as hard as Wilf and was not relabelled a new target. **Screened unresolved; not selected for further proof investment.**

## Early duplicate and classical/successor screens

The initial streaming all-date screen hashed and scanned 127,967 files, including all selected SUMMARY/discovery/FINDINGS/PROOF/review/ledger files, SCREENED-OUT notes and textual tools/scripts/agent/openproblem files inside copied review trees. The final expanded extension coverage and exact corpus count are in duplicate-audit.json. There was no 300-result truncation of this local screen. ArXiv-ID regexes have literal dots with positive/negative controls; numeric MathDB IDs use digit boundaries. Long-line unrelated Marashdeh hits refer to Paley capture, not numerical semigroups. Earlier numeric hits inside blob hashes/large integers were false collisions; initial logs are preserved. No lexical absence is promoted to semantic clearance.

Closest actual bodies were retrieved and read early in the attempted general reduction:

* Garloff–Wagner, JMAA202 (1996), 797–809, Theorem 1 and Theorem 4 proof: coefficientwise products of two quasi-stable polynomials are quasi-stable, with strictness qualifications. This does not characterize all multipliers g: even the degree-six identity multiplier 1+x+...+x^6 is not quasi-stable.
* Borcea–Branden, *Multivariate Polya-Schur classification problems in the Weyl algebra*, actual Theorem 1.8, Definition 1.3, Lemma 3.2 and proof. The multivariate diagonal-preserver condition is substantially stronger than what the present source tests provide; an explicit exact failure of the attempted extension is below. No claim that the classification solves Kudra is made.
* Froberg–Gottlieb–Haggkvist, *On numerical semigroups*, Semigroup Forum35, 63–83, actual Theorem20 and proof: in modern notation, genus<=t*n (equivalently conductor<=(t+1)*n). Its injection into pseudo-Frobenius numbers is not the requested type<=e-1+sigma bound. Retrieved the publisher-linked PDF through its normal advertised link; no access challenge, endpoint bypass or retry.

Bounded live searches for Kudra idealizer proof/counterexample and Marashdeh type-conjecture successors found no additional candidate proof body to compare. This is NOT an absence certificate; MathDB zero solutions were not used as novelty evidence.

## Full-scope proof attempt and exact point of failure

Write f(x)=E(x^2)+x O(x^2). Hermite–Biehler reduces quasi-stability to negative-real-rooted E,O in the required relative interlacing order. For a coefficient multiplier b, the desired arbitrary-degree sufficiency would establish that

    E -> sum b_(2j) E_j t^j,
    O -> sum b_(2j+1) O_j t^j

preserves that order for every source-admissible E,O, including repeated roots, proportional pairs and unequal degrees. The even Q tests control each multiplier separately; the odd tests control binomial test pairs and their shifted windows. Individual real-rootedness does not by itself prove relative order for arbitrary pairs. The same issue persists for strictness and boundary degeneracies. Source Theorem10 covers the identical-even/odd-multiplier case; using it alone would be a parameter restriction already public in this source.

I tried to transfer this to an unrestricted multivariate stability preserver. The bivariate test polynomial H(z,w)=1+2z+2w+zw is stable: a zero would require w=-(1+2z)/(2+z), whose imaginary part is -3 Im(z)/|2+z|^2<0 when Im(z)>0. But its separate homogenization K=uv+2zv+2uw+zw vanishes at

    z=-6+i, u=6+i, w=i, v=(-4+3i)/5,

all strictly in the upper half-plane. Thus stability of the tested H cannot justify stability of the larger symbol needed by this proposed diagonal-preserver route. The example even corresponds to the known stable cubic coefficient sequence (1,2,2,1). It is an objection to the stronger reduction, **not** a counterexample to either Kudra conjecture. Actual classical multiplier classification was compared rather than credited for an automatic application.

## Bounded exact validation and strongest falsifier

`sh run.sh` executes unchanged packet/helper_guard.py with AS/groupRSS512MiB, CPU210s, wall230s, nominal40ms and BLAS1. check.py uses rational Gaussian determinants and exact polynomial root counts; no floating roots or tolerance. The fixed seed110 examines 90 positive coefficient lists in degrees6,7,8; 18 pass every source Y window test. For each it verifies 12 stable inputs constructed as products of positive linear/quadratic factors, and checks every Hurwitz leading principal minor of each product. All 216 pairs pass. It also verifies the exact nonstable identity multiplier minors (1,0,0,0,-1,-1) and the upper-half-plane zero of K. These checks are bounded diagnostics and are not proofs of either conjecture. Random lists failing Y are not source counterexamples.

**Strongest objection:** a g can pass all binomial/shifted tests yet fail relative interlacing on a different admissible input pair. To refute Claim1 one needs a positive b in Y_n and an actual strictly Hurwitz input f (some m<=n) whose product has a root with positive or zero real part. For Claim2 a quasi-stable input suffices, but the full correct Y_n^star membership must be proved. No such witness was found. To prove either claim, a uniform theorem supplying precisely the missing interlacing/strictness implications is still required. No helper or bounded instance closes that quantifier.

## Registry/freshness HOLD

No registry network request was made in r110. r106 and r107 recorded single API HEAD403 rate limits at20:10/20:14; r105 Omega tree403 is retained. Their recorded receipts do not provide reset headers, so no reset was inferred. Last-known Omega73a5033dd654a16a14fcd1b13277f1a03d81d826 (commit19:55:36) and OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a (observed20:05) are inherited observations, not current certificates. Complete18:13 path inventories and bounded short chains are not semantic clearance; the old aggregate300-cap remains unresolved. Current priority and full semantic registry comparison remain HOLD independently of the mathematical gaps. No merge-time or absence-grep priority inference.

Final audit outcome: 236,196 files; manifest duplicate-corpus.jsonl. The expanded first attempt failed with MemoryError during final JSON serialization (audit-failed.guard.json); initial successful screen and failed-empty manifest are retained. Repair streams each hash record to JSONL and passes the same guard. No caps raised.
