# Steering addendum — broad scouting completed

After preserving the original report under pre-steering-discovery.md,16 attributed leads were triaged across discrete/structural subjects. The ranked five-lead shortlist is in SCOUTING.md, with exact dispositions in scouting.json. Four new bounded-screen targets: veto-core exact distortion, all-even height rigidity, G-stable Kneser classification and conditional Macdonald compression. The prior Jacobi–Stirling analysis below remains unfinished and is not promoted. No full proof route or discovery nomination. Final manifest/verification now covers both phases.

# r213 — one fresh bounded-screen target, unresolved; zero nominations

Root alone accepts/counts/stages. Administrative counts remain9 additional /39 total,next40. No ordinary full proof/refutation, PROOF.md, Lean or manuscript is proposed.

## Literal source and chronology

Ira M. Gessel, Zhicong Lin and Jiang Zeng, *Jacobi-Stirling polynomials and P-partitions*, arXiv:1201.0622v2, Conjecture15 printed p17: for EVERY integer k≥1 and EVERY integer0≤i≤k the polynomial A^old[k,i](t) has only real roots. Their Theorem1/Eq1.10 defines

    JS(n+k,n;z)=sum_i p[k,i](n) z^i,
    sum_(n≥0) p[k,i](n)t^n = A^old[k,i](t)/(1−t)^(3k−i+1).

The current Ma–Wang convention removes the common factor t: A^old[k,i](t)=t A[k,i](t). This changes the zero at0 and no other zeros. A[k,i] counts descents without the final sentinel over all Jacobi–Stirling permutations after deleting exactly i barred letters, with barred j<unbarred j<barred(j+1). Repeated unbarred j must enclose only larger letters. All deletion sets are summed, not just a fixed set. Its degree is2k−i−1. The k=0 convention, if included in a broader reading of the source, is the trivial constant numerator1, uncredited.

Actual current abstract https://arxiv.org/abs/1201.0622 lists v1 January3 2012 13:05:41UTC and v2 June22 2012 12:32:35UTC. Frozen current https://arxiv.org/pdf/1201.0622 identifies v2, but its internal date is October29 2018: this inconsistent internal timestamp is retained, not silently converted to a third version. The later bibliography cites European J.Combin.33(2012)1987–2000. The journal DOI/body were not authenticated. Crossref's exact-title query returned irrelevant records; neither DOI is assigned to this paper. DOI alias10.48550/arXiv.1201.0622 is covered by the identifier screen.

Shi-Mei Ma and Ming-Xin Wang, *Binomial expansions of Jacobi–Stirling numbers and real-rootedness of Jacobi–Stirling descent polynomials*, arXiv:2610.03111v1, current abstract submitted October2 2026 10:29:30UTC, onlyv1. Actual latest https://arxiv.org/pdf/2610.03111 identifiesv1. Theorem2 covers i∈{1,2,3,k−2,k−1}; original endpoint casesi=0,k were already known. Corollary2 proves every nonzero nonnegative combination of fixed-set polynomials in those five families has simple negative roots. None of these public outcomes is nominated. Remark1 explicitly leaves a fourth-deletion interlacing problem. No journal version authenticated. DOI alias10.48550/arXiv.2610.03111 covered by identifier screen.

Lin–Ma–Zhang, *Plateaux on generalized Stirling permutations and partial gamma-positivity*, arXiv:2005.06689v1, actual body dated14May2020; abstract history records submission13May2020. The target bibliography identifies their later *Statistics on multipermutations and partial gamma-positivity*, JCTA183(2021)105488; no journal-body identity or equality-of-bytes provenance inference is asserted. These are aliases, not two independent proofs.

Exact URLs, live retrieval UTC, hashes, original/frozen-copy paths and HTTP status are in http.jsonl and scientific-bindings.json. All source bytes were copied and both hashes verified BEFORE extraction/read. Work used frozen copies. Actual retrieval clock is October30UTC although environment calendar is October29 local.

## Actual closest proof bodies and classical applicability

Read Gessel–Lin–Zeng definitions and Theorems1–2, Section2 recurrence/properties, Section3 partition definitions and counting passages, both actual Section4 bijection/recurrence proofs, and final Conjecture15/Brenti/Haglund–Visontai discussion. No audit of all Section5 diagrams is claimed. It explicitly reports experiments only throughk=9 and observes that fixed-S real-rootedness does not give summed-i real-rootedness.

Read Ma–Wang introduction and full Section4: actual insertion equations8–10, degree11, real-root preservation Lemma2, partial-fraction proof of both Lemma3 comparisons, five comparator inductions, sign/degree completion, Corollary2, Remark1 and Proposition1. The signed-partition expansion proofs are not needed for this target. Section5's top-heaviness result is known source content, not a new nomination or substitute for real-rootedness.

Read Lin–Ma–Zhang definitions/Theorem1.3/Remark1.4, grammatical proof structure and generalized Foata–Strehl orbit proof, and actual full Section3 proof of Theorem3.1, Lemma3.2, diagonalization of the fixed-multiplicity stable polynomial, Corollary3.3. Its fixed-multiplicity, fixed-plateau specialization has a complete bridge: differentiate in the plateau variable, reverse it if necessary and differentiate again to extract a coefficient, specialize an ascent variable to1, and obtain a univariate real-rooted fixed-plateau polynomial. The multiplicity vector m(S) encodes ONE deletion set S. Summing over different m(S) proves partial gamma-positivity because nonnegative gamma coefficients add, but real stability is not closed under arbitrary sums. Its coefficient extraction holds the multiplicity vector fixed; it does not extract the number of deleted barred labels across all m(S). Thus no complete bridge from this actual theorem to the all-i source claim has been established. We do not exclude the target as routine on the grounds that its methods look classical or short.

## Sustained full-scope route and precise gaps

For L≥0 define D_L f=(1+Lx)f+x(1−x)f'. A word of lengthL with h descents has h+1 gaps preserving h and L−h gaps increasing it, proving this identity for either an inserted maximum singleton or adjacent maximum pair. The maximum pair must be adjacent, and removing it plus a retained barred maximum reverses the construction. Therefore, for all k≥2 and0≤i≤k,

    A[k,i]=D_(3k−i−2)( D_(3k−i−3) A[k−1,i] + A[k−1,i−1] ),

where nonexistent indices are zero; A[1,0]=1+x,A[1,1]=1. This is a universal exact identity, not an inference from tests.

D_L preserves simple negative-rootedness when L exceeds the input degree: at each negative simple root r of f, D_L f(r)=r(1−r)f'(r) alternates sign; the signs at0 and−infinity add the two outer intervals; its positive leading coefficient (L−deg f) gives exactly deg f+1 distinct roots. This is the actual source Lemma2 bridge.

A plausible full-scope sufficient lemma is that for EVERY k≥2 and1≤i≤k−1 the two actual equal-degree polynomials

    B=D_(3k−i−3) A[k−1,i],   C=A[k−1,i−1]

are compatible: every nonzero aB+bC with a,b≥0 has only real nonpositive roots. Together with the endpoint recurrences and the D_L lemma (extended to multiplicities by a limiting argument), this would inductively prove the full source endpoint. This universal compatibility lemma is NOT proved. Real-rootedness of B and C separately, or tests of B+C, do not establish it. A common interlacer would suffice, but none is constructed in all parameters.

The latest source's more specific Remark1 asks for

    D_(3k−7) A[k−1,4] ≺ A[k−2,0]  for every k≥5.

The known i=3 comparison places A[k−1,3] below the same comparator; its common signs would force the sum inside the fourth-deletion recurrence to be real-rooted, and D_L would finish i=4. This would resolve only a further infinite family, NOT the full all-i conjecture. Source Lemma3 compares D_L f with D_L g or D_(L+1)g when degrees differ by1. It does not compare the two equal-degree B,C above, nor remove an insertion from just one side. Even f=1,g=1+x with f≺g does not imply D_L f≺g for L>1: −1/L>−1, the reverse required order. This blocks the naive induction shortcut, not the source claim.

A second attempted full-scope route is real stability of F_k(x,z)=sum_i A[k,i](x)z^i, followed by coefficient extraction as in Lin–Ma–Zhang. It fails EXACTLY at k=2:

    F_2=(1+14x+21x²+4x³)+z(2+12x+6x²)+z²(1+2x).
    F_2(x,−2)=1−2x+9x²+4x³.

This cubic has discriminant−4192<0, hence a nonreal conjugate pair. A nonzero specialization at a real z of a real stable polynomial would be real stable by the actual source Lemma3.2; a univariate real stable polynomial is real-rooted. Therefore F_2 is not real stable. Each individual coefficient remains real-rooted. This is an exact obstruction to this chosen stable lift, not a counterexample to Conjecture15, not a claim that every possible stable lift fails, and not an eligible new discovery. The elementary positive-coefficient example (x+1)(x+2)+(x+10)(x+11), discriminant−320, independently illustrates why summands alone give no bridge.

## Exact checks, screening and limits

checks-bounded.py uses integer coefficient insertion operators and exact SymPy Sturm root counts for all54 A[k,i] with1≤k≤9. It verifies squarefreeness and degree-many negative roots. Exact rational isolating intervals (width≤10^−12), Sturm exclusion of f-roots inside each comparator interval, and alternating endpoint signs check Remark1 for5≤k≤9. Direct enumeration inserts actual ordered letters/pairs for all deletion sets throughk=3 and independently recovers all polynomial coefficients. Total counts match (3k−i)!/(3^(k−i)2^i i!(k−i)!) throughk=9. These checks do not expand the original source's all-i reported range9 and are not a proof of unbounded compatibility. Discriminant controls are exact, not floating point.

Canonical indexes fromr209/r210/r211 were combined by qualified ORIGINAL path and current originals refreshed:1,589 paths, nine changed/new local snapshots. Unchanged supplied canonical snapshot references were independently hash checked rather than duplicated. Exact aliases remain separately qualified aliases; no copied-history promotion or byte-equality provenance inference. Actualr111–113 original paths are retained, confirmed by historical-coverage.json. Required rootr209/r210/r211 decisions andr210/r211 SUMMARY/discovery were read. Analyticalr212 was not opened or changed.

Early exact title/arXiv/author aliases screened before investment; the pattern-covers lead immediately hitr108, and finite-field circular permutations hitr41. Pattern-cover bytes were unnecessarily downloaded after that screen; retained UNUSED as reconnaissance, never promoted to a fresh slot. No re-investigation of those families. Final screen adds original1201.0622, latest2610.03111, companion2005.06689, names and statement aliases; zero qualified hits. Aliases separately screened. Live arXiv exact phrase searches return the target and partial-gamma companions; actual bodies were compared above. Neither search results nor cached history authenticate current complete public proof-registry heads/bodies or all-history clearance. Journal bodies, exhaustive citing literature, specialist databases and worldwide priority remain gaps.

Inherited GitHub API/raw/codeload/diff/patch, ScienceDirect, Google challenge and MSE3499670 denials respected without retry. No browser, proxy, TLS disabling, external messages/posts/uploads, MathDB write, git, shared edits or count changes. No parked historical merge-tree/capped interval reopened. All substantive helper/retrieval/extraction/edit/hash/check commands ran through the prescribed guard with thread1, no bytecode,512MiB AS/sampled group RSS,210CPU,230wall; initial native read-only inventory/instruction reads disclosed in FAILURES.md. Caps unchanged. Exact failures are preserved, including a204-second extended check that reached JSON serialization failure; its unrecorded intermediate calculations are not promoted to evidence. A corrected smaller checker passes and is replayed separately.

Final manifest excludes itself and verification-receipt.json EXPLICITLY. A separate guarded verifier after final writes verifies all scientific original/copy hashes, external canonical historical/index snapshots, corrected checker replay, byte-exact text re-extraction and every manifest entry including a complete file-set comparison. Administrative ledger/NEXT/context are point-in-time snapshots, not live immutable scientific premises. Historical original drift is reported separately. No full nominee; the universal compatibility or other full-scope proof remains missing.
