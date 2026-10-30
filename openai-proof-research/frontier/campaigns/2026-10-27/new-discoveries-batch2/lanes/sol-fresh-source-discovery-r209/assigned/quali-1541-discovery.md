# Easlick’s maximum-cycle question: unresolved

## Exact source and quantifiers

The frozen actual primary is Terry Easlick, *Computer-Assisted Results for n-Sided Non-Transitive Dice Taking Face Values in [n]*, arXiv:2610.40321v1, Section 3, Conjecture 1, PDF page 7. Sections 1–3, the concluding discussion and the relevant enumeration code were read. The abstract history lists only v1, submitted October 29, 2026 at 15:54:42 UTC; the PDF’s internal date is October 30. Retrieval timestamps are actual UTC from the runtime, October 30, despite the session’s supplied October 29 local date. Exact URLs, headers, byte lengths and SHA-256 values are in retrieval/ and scientific-bindings.json.

For each integer n ≥ 3, let V_n be the nondecreasing n-tuples with entries in {1,…,n}. Each tuple represents a fair die, repeated labels allowed, and distinct vertices mean distinct multisets. Set

    W(A,B) = #{(i,j): A_i > B_j},    T_n = floor(n²/2) + 1.

Let G_n have an edge A → B exactly when W(A,B)=T_n. These are the uniformly minimal-winning edges, with strict winning probability T_n/n². The source’s Definition 2 requires distinct vertices in each cycle. Let c_n be the maximum simple directed cycle length, taking zero if there is no cycle. The literal Conjecture 1 says that 6 is the largest integer n ≥ 3 for which c_n=n. With its Theorem 1, the unresolved assertion is

    for EVERY integer n > 6, c_n ≠ n.

The paper supports this by exhibiting cycles longer than n for n=7,8,9,10. Merely exhibiting an n-cycle would not refute it. A sufficient full route is c_n>n for every n≥7; this is stronger than the literal residual assertion. No assertion about c_n is inferred from the size of a strongly connected component alone.

## Closest public proof and the full applicability comparison

Joshua E. Rooney, *Winning Probabilities of Balanced and Nontransitive n-tuples of Dice*, arXiv:2505.21950v1, Theorem 1.2 and its Sections 3–4 proof, was read from the frozen actual PDF. The current abstract lists only v1 (May 28, 2025); the unversioned PDF response explicitly identifies v1. It predates Easlick. This is a closer body than merely invoking a generic tournament-realization theorem: it realizes every rational winning probability p in (1/2, π_l], where π_l=1−1/(4 cos²(π/(l+2)))), for l dice, with some common face count m. For l≥3 and our n≥7, T_n/n²≤1/2+1/49<π_3, so its probability range includes the desired value. Reversing the ordering of dice gives the source’s winning orientation.

Its proof chooses m to make mp and several other rational products integers, then constructs a central word with m occurrences of each of l letters and assigns consecutive, distinct labels 1,…,lm. Transpositions adjust adjacent pair counts one unit at a time while preserving the others; Lemma 3.2 supplies the interval of attainable counts. The rational approximation argument in Lemma 3.3 selects auxiliary proportions strictly inside the admissible intervals. Thus the theorem gives an exact balanced cycle with that p, but does not prescribe m=n, nor labels in [n].

Here the obstruction to that particular adaptation is explicit. gcd(T_n,n²)=1: if n is odd then 2T_n=n²+1, so a common divisor divides 1; if n=2k then T_n=2k²+1 and gcd(2k²+1,4k²)=gcd(2k²+1,2)=1. Hence the proof’s condition mp∈Z requires n²|m, and m≥n². The resulting word has lm distinct labels. A strictly order-preserving relabeling retains lm ranks and cannot compress it into [n]. Allowing ties or deleting faces can alter the actual pair counts; no preservation theorem is provided. This is a full explanation of the failed bridge, not an exclusion based on proof length. It does not show no different classical bridge exists. The separate Schaefer–Schweig, Angel–Davis and 2024 Kim et al. bodies were not obtained; Rooney’s cited summaries do not substitute for them. No routine-corollary exclusion or priority certification is claimed.

## Sustained construction route: exact padding and its obstruction

For every even n and EVERY vertex D∈V_n define P(D)=(1,D_1+1,…,D_n+1)∈V_(n+1). This map is injective. For every ordered pair D,E,

    W(P(D),P(E)) = W(D,E) + n.

Indeed, old-old comparisons are unchanged, all n shifted faces of D beat E’s new 1, D’s new 1 beats no face, and the two new 1s tie. For even n, T_(n+1)−T_n=n. Consequently P embeds every minimal-winning directed cycle in the next graph, preserving its length. In particular c_(n+1)≥c_n for even n. This does not increase the cycle length, and only covers one parity transition.

The more ambitious common-padding route fails universally, not just in a finite example. Suppose D_1,…,D_l is any cycle of n-face dice and add the SAME r-face multiset Q to each die, keeping old comparisons unchanged. Write τ(D,Q) for the number of equal-label pairs between them. The elementary identity

    W(D,Q)+W(Q,D)=nr−τ(D,Q)

gives, after summing cyclically,

    Σ_i [W(D_i∪Q,D_(i+1)∪Q)−W(D_i,D_(i+1))]
       = l(nr+W(Q,Q))−Σ_i τ(D_i,Q)
       ≤ l(nr+r(r−1)/2).

The equality uses only reindexing the cyclic sum; the inequality uses nonnegative tie counts and at most one strictly ordered pair for each unordered pair of distinct faces in Q. To preserve every edge at the new minimal threshold, the left side must equal l(T_(n+r)−T_n). If r is even, this threshold gain is nr+r²/2, exceeding the bound by r/2 per edge. If r is odd and n is even, it is nr+(r²−1)/2, exceeding the bound by (r−1)/2. If r and n are odd, it is nr+(r²+1)/2, exceeding it by (r+1)/2. Thus all r≥2, and also r=1 for odd n, are impossible for common padding. The surviving r=1, even-n case is exactly the construction above when the added face is below every old face.

This argument permits arbitrary common Q and ties and even disregards the [n+r] label restriction, so failure cannot be repaired merely by choosing another common padding value. It is a method obstruction, not a counterexample to Easlick. Dice-specific insertions, cycle replacement, or a genuinely new construction remain possible.

## Exact missing lemma and strongest objections

A sufficient missing lemma is: for EVERY integer n≥11 there exist l≥n+1 distinct vectors a^(1),…,a^(l) in Z_≥0^n, each with coordinate sum n, such that for EVERY cyclic i,

    Σ_(u>v) a^(i)_u a^(i+1)_v = floor(n²/2)+1.

The verified source cases n=7,…,10 then finish the stronger route. A proof would need both the fixed resource bounds and the cycle length; unrestricted probability realization supplies neither. Alternatively one could prove the weaker c_n≠n directly, but no such universal extremal argument is available. Increasing n one step at a time with common padding is now ruled out except for the one parity step and cannot solve the problem. Finite SCC computations cannot supply this lemma. There is no complete ordinary proof/refutation and no PROOF.md, Lean or manuscript investment.

## Screening and validation limits

The canonical r205 qualified ORIGINAL history index was reused, with direct top-level new/changed lane reports refreshed. The final bounded screen covers 1,539 original paths, seven changed/new, none missing. Unchanged bodies reuse explicitly bound r205 snapshots; only deltas were copied. Actual r111–113 report paths are retained in that index. Inherited aliases are retained separately (1,075 refreshed paths); no equal-byte inference of provenance or recursive promotion of generated histories was used. Exact arXiv identifiers, title, author, statement phrases and relevant DOI aliases gave no match in either screen. These bounds do not clear all earlier history. r193/r194/r197/r199/r201/r202/r203/r204 decisions and r202–204 summaries were read first. r205 and r207 were left alone.

The initial current search returns only the first 50 results for “conjecture,” across mixed categories; it is reconnaissance, not a proof registry. Many results explicitly advertise public resolutions and were not invested in. The separate current nontransitive-title search located Rooney’s body. Exact identifier search redirected to the target abstract and supplies no independent citing coverage. No current complete registry head/body screen, worldwide literature search, or MathDB status claim is available. Denied GitHub, ScienceDirect and Google challenge routes were not attempted; there were no access denials on the attempted arXiv routes.

check.py independently reconstructs G_3,…,G_7, matches the source’s vertex/edge/SCC counts, exhausts cycles only through n=6, and obtains an exact 14-cycle at n=7. It checks common-low padding on all 213,444 ordered pairs of six-face dice and bounded integer threshold/common-multiset identities. These controls are finite arithmetic verification, not a full proof. The all-parameter padding arguments above are ordinary deductions, uncredited helpers. Source claims for n=8,…,10 were read but not independently enumerated here.
