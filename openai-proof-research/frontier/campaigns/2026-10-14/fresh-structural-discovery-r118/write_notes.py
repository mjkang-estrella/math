from pathlib import Path
import json, hashlib, re
root=Path(__file__).resolve().parent
pub=root/'packet/public'
docs={
'report.md':r'''# Structural discovery r118 — prefreeze archive

No target was frozen and no candidate is nominated. No contribution rating, correctness gate or campaign-count decision is made. This round leaves the parent's campaign unchanged. All calculations below occurred during feasibility screening, before any proposed freeze; there is no weakened replacement target or downstream formal/manuscript work.

The principal calculation is a complete compatibility reduction for source126's matrix splitting operation. De la Salle's actual arbitrary-state orthogonalization theorem, applied with the state weighted by the square of the sum, gives an absolute factor 10 instead of a family-size-dependent splitting constant. The normalization error and primary rounding error spend complementary portions of the same overlap budget. Thus a stronger splitting statement alone does not identify an unpaid compatibility operation. The calculation is retained in `orthogonalization.md`, with the primary theorem and its real-field implementation credited. No original-theorem priority claim is made.

Three other families received fresh operative-source attention: source192's Boolean observation/amplification, source185's infinite-matroid assembly and source120's factor reduction. The strongest source192 mean-cost and independent-score alternatives were read as well as its basic reporting construction. They already handle average cell cost, rare events, merged failure cells and repeated normal approximation. Neither the source report nor classical real-valued symmetrization supplies a monotonicity-preserving Boolean degree operation. Source185's finite-error ordinal descent and the older connectedization are already available; the descriptive replacement question was already investigated in r114 and still lacks an obstruction-preserving replacement for the classifier. For source120, the actual degree-three general-factor primary uses a separate feasibility oracle and quadratically many optimization calls. A near-linear prescribed-factor solver does not discharge these interfaces. These are gaps in attempted methods, not impossibility theorems for the larger questions.

The broader search also read actual historical operations for 168 (marked Bruhat data), 171 (multicolor induced cubes), 175 (saturation), 190 (ordered matrices), 180 (Hamiltonian expansion), 187 (biased Snaky), 161 (regular Sidorenko patterns), and the four-family r113 exclusions. Their reading depths differ and are disclosed. No title-only hit is treated as a proof comparison. Search outputs include large authored bodies with no size cutoff. The r114 source185 body was read late in screening, before any freeze, and supersedes an apparent fresh descriptive direction; the exact antecedent is explicitly credited.

There is no proposal to pursue an unknown central invariant merely to generate a freeze. The reusable output is the factor-10 reduction and its precise exact-sum boundary, plus more precise source/primary interfaces for future discovery. The exact-sum two-dimensional example and Boolean compression example are method diagnostics only. All source statements and operative proofs at the stipulated pin are assumed true throughout.

See `reading.md` for actual reading extents and acquisition limits, `screens.md` for operation comparisons, and `source-register.json` for the canonical pinned raw URLs, Git blobs and SHA256 identities. Private upstream, primary and historical search bodies retain their original rights. The public directory contains original prose, metadata and code only.

The detached manifest/report hashes are outside the packet in `FINAL-ANCHORS.json` and the parent-facing `REPORT.md`. The read-only verifier requires both hashes as external arguments and the complete canonical tree. Copied mutation controls and finite rational checks concern integrity and bounded identities only; neither constitutes a mathematical or contribution gate.
''',
'orthogonalization.md':r'''# A compatible matrix-splitting reduction, before any freeze

This is a feasibility/comparison calculation, not a frozen candidate. Its complete scope is finite families of positive semidefinite matrices on any finite-dimensional real or complex Hilbert space, with no commutativity, spectral gap, bounded condition number, large-parameter or subsequence restriction. Constants 10 and 20 below are absolute. It does not preserve the sum of the approximants.

## Paid source and primary contracts

Pinned source126, `splitting.tex`, proves an orthogonal splitting with off-label squared Frobenius error at most `2^(m−1) O`, where `O=sum_(i≠j) tr(A_i A_j)` and there are m labels. Its proof uses the positive/negative spectral spaces of a two-matrix difference, then induction and overlap accounting. The `matching.tex` proof uses this within smoothing and a low-degree signed pseudomoment argument. Its exact main theorem already covers every fixed shift 0<rho<1 with an exponential-rate constant independent of rho; rho=1 is explicitly a different, small diagonal factorization endpoint. The uniform matching-smoothing theorem already includes every admissible fixed-cell edge-count table, including rare and unbalanced tables. Changing those parameters is not the present operation.

Mikael de la Salle, *Orthogonalization of positive operator valued measures*, C. R. Math. 360 (2022), 549–560, [published primary PDF](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.5802/crmath.326.pdf), Theorem 2: for a POVM a_i and a normal state phi, a defect less than epsilon in `phi(sum a_i²)` yields a PVM P_i with `phi(sum |a_i−P_i|²)<9 epsilon`. The state need not be tracial. The finite-algebra proof in §3, including Lemmas 6 and 7, was read. In fixed finite dimension compactness of the set of PVMs gives the non-strict version with defect delta by epsilon decreasing to delta. For delta=0, the same limit applies.

For real matrices this is the same finite proof over real spaces, not an average of complex projections: the extremization in Lemma 6 occurs in real symmetric operators commuting with the relevant a_i; two fractional eigenvectors admit the same real rank-one perturbation preserving the total trace. Extreme effects therefore are real projections with the same total-rank bound. Lemma 7's equal-rank polar completion uses a real partial isometry extended between real orthogonal complements. The final stack/polar estimates use adjoints and positive square roots and retain the constant 9. No infinite-algebra real-form theorem is needed.

## Full normalization and budget calculation

Set S=sum_i A_i, K=sum_i tr(A_i²), T=tr(S²), and O=T−K. Each pair trace is nonnegative, hence O≥0. If S=0 all A_i vanish and any labelled orthogonal decomposition suffices. Otherwise restrict to support(S). Every A_i vanishes on ker(S), so extending a resulting PVM by assigning that kernel to one label changes none of the estimates.

On support(S), put a_i=S^(−1/2) A_i S^(−1/2). These form a POVM. Use the positive normalized state

    phi(X)=tr(S² X)/T.

Define Q=sum_i tr(S² a_i²). In an eigenbasis S=diag(s_u),

    Q=sum_(i,u,v) (s_u/s_v) |(A_i)_(uv)|².

Pairing (u,v) and (v,u) shows Q≥K, since r+1/r≥2. Since 0≤a_i≤I, a_i²≤a_i, giving Q≤T. Thus E=Q−K and D=T−Q are nonnegative and E+D=O. This last exact identity makes the two error budgets compatible.

Let R=sum_i ||A_i−a_i S||_F². For an unordered off-diagonal pair with r=s_u/s_v, the coefficient in R is

    r+1/r−2 sqrt(r)−2/sqrt(r)+2,

and the coefficient in E is r+1/r−2. Their difference is `2(sqrt(r)+1/sqrt(r)−2)≥0`. Diagonal terms vanish. Therefore R≤E without a condition-number factor.

The primary theorem gives a labelled PVM P_i with

    sum_i ||(a_i−P_i) S||_F² ≤ 9D.

The weighted state is exactly what produces this right-multiplication norm; cyclicity of the trace gives the displayed equality of norms. Applying the triangle inequality in the direct sum of Hilbert–Schmidt spaces, followed by Cauchy–Schwarz in two coordinates,

    sum_i ||A_i−P_i S||_F²
      ≤ (sqrt(E)+3 sqrt(D))²
      ≤ 10(E+D)=10O.

For s≠i, P_s(P_i S)P_s=0. The orthogonal diagonal block projections are jointly Hilbert–Schmidt contractive, so

    sum_i sum_(s≠i) ||P_s A_i P_s||_F² ≤10O.

If actual positive orthogonal approximants are desired, take B_i=P_i A_i P_i. Their supports are orthogonal. For Hermitian A_i, the block decomposition gives

    ||A_i−B_i||_F² ≤2||(I−P_i) A_i||_F²
                       ≤2||A_i−P_i S||_F².

Consequently sum_i ||A_i−B_i||_F²≤20O. This is another consequence of the same compatible reduction, not a separate discovery.

The arbitrary-state theorem supplies the needed simultaneous projections; the square-sum state and elementary spectral identities transfer exactly to the source's unnormalized Frobenius overlap. There is no remaining operation in this splitting comparison to nominate. Improving the internal constant does not itself improve the source's exponential PSD-rank scale or create a new matching theorem.

## Why exact preservation of S is a separate boundary

Let 0<e<1, c=sqrt(1−e²), and

    A1=[[1,0],[0,0]],       A2=[[e², ec],[ec,c²]].

Both are rank-one projections. Their overlap budget is O=2e². S=A1+A2 has distinct eigenvalues 1+e and 1−e, with projections Pplus/Pminus=(I±(S−I)/e)/2.

If B1,B2 are positive, B1 B2=0 and B1+B2=S, then S B1=B1²=B1 S. Because S has simple spectrum, each S eigenvector belongs entirely to one B label. Thus B1 is one of 0, S, (1+e)Pplus, (1−e)Pminus; B2 is its complementary part. Direct substitution yields

    ||A1−B1||_F²+||A2−B2||_F²=2

in all four cases. Therefore no absolute multiple of O can control this error while preserving S exactly for all e. This refutes only that additional exact-sum estimate. It is not a refutation of the compatible splitting bound, a new nominated theorem, or a repair of any previously frozen scope.

The rational finite diagnostic chooses e=2t/(1+t²), c=(1−t²)/(1+t²) for t=1/k. The displayed algebra proves the general statement; the diagnostic verifies only the listed finite examples.
''',
'screens.md':r'''# Other structural/discrete screens and precise interfaces

All entries are prefreeze. No complete monotone-Boolean, descriptive-matroid or fast general-factor target was frozen. Method obstructions below are not universal impossibility results.

## 192: reporting, mean cell cost, and monotonicity

The source's basic report uses a selector i(u), leaf interval tests, B=all leaves passing, P=all unselected leaves passing and A=P minus B. Its indicator expansion subtracts B from a sum of selected-index terms, saving one coordinate in every cell's algebraic degree. This is an exact pointwise indicator identity, not a decision-tree query bound. The retained conditional score on the rare event has variance saving, and the source already gives finite iteration and final Boolean readout without losing the indicator degree.

The actual alternatives are stronger than just this basic rule. `lem:coarse-report` merges all-pass reports into one mark and computes their exact loss, leaving positive gain. The independent-extra-input rule has `eq:switching-variance` and `eq:switching-correction`: q+p(1−Var(L|A)), with correction from the chosen predictor to the conditional mean. `lem:refinement` makes a finite grid on A's complement so retained variance exceeds average cell cost. `thm:mean-cost` retains whole label words under a total-cost threshold and merges the other words into one failure label. The complement identity bounds failure-label degree; a fourth-moment bound for the fixed finite observation controls its variance loss, and a CLT plus L2 closeness restores the iteration invariant. `lem:mc-transfer` requires no fourth moment for its fixed-partition first-moment transfer. These full operations were read; heterogeneous costs, rare cells and repeated CLT restoration are already supplied.

The direct reporting score does not preserve coordinate monotonicity. Fix u and all unselected leaves inside their intervals. As the selected leaf moves below/through/above its interval, the report is A, B, A. The A score is the same constant on both sides; the B score changes with the selected leaf. A nonconstant function with equal constant tails cannot be monotone. This concerns the score operation, not every possible final threshold sign and not all alternative constructions.

A classical Boolean coordinate compression also fails to preserve degree in general. The multiplexer

    f=(x2+x3)/2+x1(x2−x3)/2

is Boolean of degree two. Sorting each x1 pair into increasing order replaces its linear coefficient b by |b|=(1−x2*x3)/2. The resulting Boolean function

    g=(x2+x3)/2+x1(1−x2*x3)/2

has degree three. This only defeats this compiler. In particular it is not a counterexample to a monotone influence bound.

The actual [Filmus–Hatami–Keller–Lifshitz v3](https://arxiv.org/pdf/1404.3396v3) Lemmas 3.14–3.15 preserve total L1 influence by averaging a monotone real-valued function over permutations and then comparing a univariate polynomial. Theorem 3.16 is for values in [−1,1], not just Boolean values. The averaging loses Boolean values; applying sign has no general Fourier-degree preservation (a linear sum's sign can be majority of full degree). Thus it supplies no missing Boolean compiler. R25's complete cyclic-disjointification and wreath-product comparison was read; it already retains source conditional laws under cyclic symmetry. Renaming that construction as a symmetry extension would not supply a new operation. A genuine monotone event/indicator amplification with positive variance advantage remains unbuilt here.

## 185: ordinal descent versus a regular replacement

The pinned `lem:selfdual-reduction`, `lem:columns`, `lem:ultrafilter`, `lem:thinning`, `lem:reservations`, and the full double-ray counterexample were inspected. The two parity direct sums place a self-dual local matroid on adjacent countably infinite bundles. An alleged independent covering propagates an ultrafilter-large part outward and forces a strict infinite ordinal descent (`eq:ordinal-descent`). Finite changes do not affect the two relevant ideals/ranks. The consequences section's universal packing/covering failures are already paid.

R21's actual checkpoint constructs connected self-dual counterexamples by standard elongation followed by truncation. Its proof preserves the descent under finitely many errors in each local component, not merely a uniformly bounded total error. R32 also records this antecedent. Bowler–Geschke's [author version dated 6 October 2014](https://www.math.uni-hamburg.de/home/geschke/papers/UniformMatroid7.pdf), Lemma 4, Theorem 6, complete Theorem 8 and Theorem 10 proofs were read. Theorem 8 says a uniform matroid that is neither finitary nor cofinitary is infinitely connected. It does NOT say that arbitrary source direct sums become infinitely connected or supply a tameness theorem. Its uniform exchange argument and the primary truncation definitions already account for the obvious connectivity routes.

R114's `screen-185.md`, read late before any freeze, already asks the Borel-independent-family question and examines the source classifier plus determined circuit games. Its auxiliary free ultrafilter cannot itself be Borel, by finite-change invariance/zero-one law and complement symmetry. That does not prove the final independent-set family non-Borel. Its actual primary circuit-game comparison has finite local pieces/overlap-one interfaces different from the source's infinite bundles and local Q. This round did not newly read the circuit-game primary or solve that interface. No obstruction-preserving regular replacement was constructed, and neither a tame nor a finite/local substitute is offered. This direction is an inherited open interface, not a newly discovered question.

## 120: factor networks and the actual general-factor oracle

Pinned `thm:main` already gives one uniform randomized word-RAM program for explicit maximum cardinality matching, with every-path input-size almost-linear bound, charged randomness, arithmetic, unsuccessful computations and output. `factor:reduction` and `cor:f-factor` already give prescribed-degree factors through incidence ports and logarithmic-size rearrangeable networks. The exact f array is part of the input. The reduction proof and main interface were freshly read; the entire matching backend was not reread.

R35's signed-weight attempt lacks a weighted dual invariant; two expensive odd bins can expose the cost of losing their internal edges. R111's actual interval/parity factor reduction already uses dummy vertices and matching-realizable degree sets. Those are prior operations, not fresh weighted or general-factor work.

The strongest further primary examined was Shao–Zivny's [ISAAC2023 author preprint](https://www.cs.ox.ac.uk/standa.zivny/publications/sz23isaac-preprint.pdf), particularly Theorem 5 and Lemmas 7–8/Algorithm 1 interfaces. Its degree-three exceptional types are {p,p+1,p+3} and {p,p+2,p+3}, split into a parity pair D0 and a singleton D1. The recursive algorithm assumes a *Decision oracle for the enlarged general-factor class*, in addition to Optimization for matching-realizable restrictions. It invokes up to n Decision calls and quadratically many Optimization calls. Theorem 5's local-exchange condition uses an optimum in D0; the version with an optimum in D1 is not supplied. Thus substituting a fast prescribed-factor solver neither supplies that Decision oracle nor batches the quadratic calls. The short version refers its central structural proof to the full paper, which was not newly acquired here. No theorem depending on that unread proof is claimed. A truly subpolynomial-call/witness-preserving implementation remains absent, as does a full weighted matching reduction.

## Further actual history, unequal depth

* 168: r111's marked-generator/parabolic comparison already covers the apparent simple recurrence extension; its full screen was read. No fresh primary proof was acquired here.
* 171: r32's full screen and actual later r114 operation passages exclude all-r linear growth (the first-moment obstruction for r>=5), and distinguish the unresolved r=3,4 density/label budget. R48 was searched, not reread completely. No sparse-host repair is substituted.
* 175: r111's complete screen already supplies a compatible heterogeneous-component saturation construction; no new parameter variant was pursued.
* 190: r23's checkpoint already computes the bounded row/column VC-dimension transfer and compares the smaller ordered matrix result. Its primary is historical evidence here, not a fresh full primary read.
* 180: the large I164 body was content-searched and its square-expansion/signed-state passages inspected; the full output truncated. Hamiltonian counting/affine-span extraction was not closed. It is not classified from a title.
* 187: r101's working-threshold body distinguishes the paid biased Snaky response from remaining biases. No new response tree was produced.
* 161: I13's actual regular-pattern identity explains why the regular score collapses; the full combined display truncated and is not treated as full-family clearance.
* R113's actual report excludes its existing 176/130/238/097 routes. I198's source095 regularization discussion was inspected as an exclusion. These are bounded history screens, not fresh full source investigations.

No negative author verdict was used as the reason to stop a family. The reasons are the actual compatible operation or the precise unconstructed interface above. None asserts exhaustive literature clearance.
''',
'reading.md':r'''# Reading, provenance, chronology and limits

## Context and history

AGENTS.md and sources/upstream.json were read. The complete sources/preprints-tree.json was parsed and every entry traversed: 13223 entries, 10373 blobs, 2850 trees, truncated=false. Its SHA256 is eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. The truncated sources/tree.json was not used. The complete CONTENTS.md was loaded and parsed; heading inventories and selected family descriptions were displayed, with some combined display truncation. This is not a claim to have semantically read every abstract or manuscript.

NEW-TEN opening/current requirements, heading navigation, selected operation hits and the final 65 lines were read, not all 1838 lines sequentially. R023–R040 finding bodies were read in batches; missing R025/R026 portions were repaired in smaller displays. Their linked manuscripts and reviews were not all reread. The actual r117 report/structural-screens/online-fairness/automata/reading bodies and r116 report/screen118/screens157186/history/reading were inspected; a small r117 fairness phase paragraph was lost in combined truncation. These are exclusions, not independently verified full results. The actual T152AC116 contribution review and reading-limits were inspected, with the middle section recovered separately. Arithmeticr80 research and reading-limits were read; the final reading-limits display lost a few hundred characters near its terminal source/code discussion. Analyticr115 report/operation comparison was inspected but its whole reading ledger was not reread. The supplied cross-lane summaries retain their stated limits.

Actual historical bodies read include r21 candidate and checkpoint; r23 checkpoint; r25 candidate and primary-comparison; r32 screen171 and history-and-disposition; r35 matching120 (small display-tail limit); r75 comparison/progress (combined display limits); r101 working-threshold; r111 screens120/168/175; r113 report; and r114 screen185. R114 screen171247 and r48 were content-search passages rather than whole-document reads. I198's first 165 lines were inspected; I164 and I13 substantial relevant passages were displayed with truncation and are not complete readings. Historical claims are credited to these actual bodies; their cited external papers are not counted as fresh primary reading here.

The scans used rg on campaigns, iterations and experiments, including source aliases, construction names and primitive-operation words. Retained private `search-*.txt` files are exact search stdout, not proof reading. They include noisy hits and large authored files; no size cutoff was imposed. Some scans excluded copied evidence/source paths to reduce noise. The original command strings were not captured for every early scan, so they are not reconstructed as an exact command log. Final path/hash context receipts identify the main retained context files without making a full repository snapshot. Absence of a hit is not a novelty certificate. Current active-lane files were not modified.

The r114 source185 descriptive antecedent was read late in the prefreeze screen; its Borel-classifier/circuit-game interface supersedes any apparent fresh descriptive direction. The strongest source192 mean-cost proof was completed after the initial monotonicity feasibility calculation and before this archive. The source126 primary theorem and finite proof were read before completing the factor-10 transfer calculation. All feasibility calculations, including the exact-sum and compression examples, preceded any freeze. No freeze occurred at any point, and there is no frozen scope to repair.

## Pinned upstream bodies

31 TeX/Bib blobs were acquired: 30 fresh HTTP200 responses and one local matching-byte reuse, as recorded in private/upstream-receipts.json. Every blob's Git SHA1 (including its Git blob header) matches the complete tree; SHA256, canonical pin/raw URL, byte count and local location are retained. The pin is fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. All pinned proof operations are stipulated true; no truth audit was performed.

* 126: introduction, matching, parity and splitting read completely, including a repair of matching lines130–165. matching-smoothing lines1–140 read, including the full uniform theorem and its fourth-moment/counting setup; later proof not read. local-averaging/fourier-smoothing acquired but not fully semantically read; their interface appears in the read introduction/matching application. Exact labels include thm:main, cor:exact-lift, thm:matching-smoothing and the splitting labels listed in source-register.json. No fresh approximate-rank theorem is inferred from them.
* 192: 00-introduction, 01-observations, 02-reporting, 03-alternatives, 04-mean-cost read fully. 05-weighted and 06-small-width acquired but not read in full; label/navigation only. Exact operative labels include prop:amplification, lem:readout, lem:gaussian, eq:indicator, lem:coarse-report, eq:switching-variance, eq:switching-correction, lem:refinement, thm:mean-cost and lem:mc-transfer. The unseen appendices are not claimed to rule out every possible monotone mechanism.
* 185: 01-introduction, 02-matroids, 03-filters, 06-counterexample, 07-consequences read fully. 04-local-bases first140 lines read; 05-assembly acquired but not semantically read. The full basis construction is stipulated, not audited. Labels include lem:selfdual-reduction, lem:columns, lem:ultrafilter, lem:thinning, lem:reservations, eq:ordinal-descent. No descriptive regularity of the final basis family is inferred from the classifier alone.
* 120: 01-introduction and 10-f-factors read fully (the factor-file tail was recovered after one filename typo produced a local not-found error). 03-matching-state acquired but not fully reread; label search is not semantic reading. Labels thm:main, factor:reduction, cor:f-factor. Whole backend proofs were not acquired here.

The complete tree was used to identify the selected source directories and their companion inventory. This is not a claim to have semantically read every same-family file. All acquired-file labels are included as navigation metadata, not as a claim that each labelled proof was read.

## Successful primary acquisitions

All five acquisitions returned HTTP200. Exact URLs, PDF/text SHA256, byte counts and UTC retrieval times are in primary-register.json. Bodies are private; public notes paraphrase and derive independently. `pdftotext -layout` extraction is not visual/OCR certification. No browser UI was used. Search snippets/abstracts were navigation only. There is no failed primary download to report in this round.

1. De la Salle, published C.R.Math.360(2022),549–560, DOI10.5802/crmath.326: introduction/Theorem2 and finite proof §3 with Lemmas6–7 read, extracted lines1–approximately480; some continuation into the next section was inspected, not relied upon. The finite proof, arbitrary normal state, polar completion and constant9 are operative. The infinite-algebra proof and later applications are not prerequisites for the calculation here.
2. Shao–Zivny, ISAAC2023 author preprint at the Oxford author URL: actual Theorem5 and recursive-interface discussion/Lemmas7–8/Algorithm1 around extracted lines303–520 read, with a small combined-display truncation around part of the algorithm. Its separate Decision and Optimization contracts and call counts were visible. The full-paper structural proof and complete AppendixA were not freshly read. The main complexity theorem is not adopted as a new source fact beyond this bounded comparison.
3. Filmus–Hatami–Keller–Lifshitz, arXiv1404.3396v3: extracted lines581–710 inspected; Lemmas3.14–3.15 proofs recovered in a separate lines610–675 display. Real-valued monotone symmetrization/one-variable passage and Theorem3.16 scope were read. Earlier complete lemmas and all the transitive specialization were not newly read; r25's primary comparison was read as history.
4. Bowler–Geschke, author version dated6October2014, UniformMatroid7.pdf: extracted lines90–228 read, including Lemma4/Theorem6 and complete Theorems8/10 proofs. The later set-theoretic existence construction was not read. Theorem8 is infinite connectivity, not a wildness or tameness assertion.
5. Gollin–Joo, arXiv2504.05064v1: introduction/navigation only, requested first145 lines but combined output truncated after roughly80. Its later generalized-truncation proof was not read. It is background, not an operative theorem for a new deduction; the concrete elongation/truncation proof used as exclusion is in r21.

## Integrity boundary

The seal binds bytes and exact inventory. It cannot authenticate semantic reading, mathematical correctness, contribution or priority. The finite diagnostics check rational identities and eight Boolean values only. The copied mutation controls exercise the verifier on separate copies under the owned directory, with before/after byte-inventory checks on the original. They are not mathematical gates.
''',
'RIGHTS.md':'''# Rights and scope

Public prose and original derivation/code in this directory were written for Myeongjin Kang; no affiliation is asserted. Original prose is offered under CC BY 4.0 and original code under the MIT License. Metadata records facts about sources. These permissions do not relicense upstream or third-party materials.

Private upstream TeX/Bib, primary PDF/extracted text and historical search excerpts remain subject to their original rights. Their presence is limited local research evidence, not authorization to publish or redistribute them. Public original notes cite the actual primary/source contracts; they do not transplant proof bodies. No upload, external publication or contact occurred.
''',
'REPRODUCE.md':'''# Read-only verification

From the assigned round directory, run:

    python -B packet/public/verify.py --packet packet --finalhash <detached MANIFEST.json SHA256> --reporthash <detached public/report.md SHA256> --tree ../../../../sources/preprints-tree.json

Supply the two hashes from the outside-packet FINAL-ANCHORS.json or the parent handoff. The verifier will not use an in-packet anchor as a substitute. The tree argument must be the complete 13223-entry truncated=false tree, not sources/tree.json. The verifier does not download anything, execute tests, write files or inspect mathematical truth.

The finite diagnostic is a separate command:

    python -B packet/public/finite_checks.py

Its recorded stdout is public/finite-checks.json. These bounded identities are not theorem or contribution gates. Copied mutation controls are run by the outside-packet run_controls.py; they use temporary copies only within controls/ and retain their result outside the packet. The original sealed packet is never modified by that script.
'''
}
for name,body in docs.items(): (pub/name).write_text(body)
rows=json.loads((root/'packet/private/upstream-receipts.json').read_text())
for row in rows:
    body=(root/'packet'/row['local']).read_text()
    row['labels_navigation_only']=re.findall(r'\\label\{([^}]+)\}',body)
(pub/'source-register.json').write_text(json.dumps({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','sources':rows},indent=2)+'\n')
(pub/'primary-register.json').write_bytes((root/'packet/private/primary-receipts.json').read_bytes())
print('Wrote',len(docs),'original notes and two registers')
