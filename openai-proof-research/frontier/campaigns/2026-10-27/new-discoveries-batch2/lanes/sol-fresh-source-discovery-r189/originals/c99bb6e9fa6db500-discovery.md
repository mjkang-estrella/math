# r65: Latin-square ascent distribution — unresolved, credit 0

## Exact target and four-claim screen

1. Byun–Poznanović, arXiv:2604.14639v1, Conjecture 1.1: immediately discarded at context reconciliation. This is the previously investigated powered-binomial family (r15/r2), not a fresh lane target. No new experiments or result on it.
2. Ai–Gutin–Lei–Yeo–Zhou, Journal of Graph Theory 110 (2025), 127–131, DOI 10.1002/jgt.23257, Conjecture 4.1: excluded by actual Afonso–Colucci–Naia arXiv:2606.24739v1 proof. Their exceptional diameter-four trees attach h incoming and h outgoing leaves to each of three path vertices, with both central edges away from the middle. The primary proof groups embeddings by the three centers and balanced pendant choices: transitive triples have two source-centered and two sink-centered maps; cyclic triples have neither. These trees have 6h+3 vertices, are not self-converse, and cannot result from bridge-mirroring, which doubles vertex count. Complete concrete subsumption, not a title match. Read journal PDF pp128–131 and counter-source section4.3 proof bodies.
3. Lundström–Saud Maia Leite, published EJC133 (2026)104304, Conjecture3.7: excluded by the same authors' arXiv:2504.05123v5 (1 October2026), Theorem3.12. The current source proves the f-vector log-concavity previously conjectured in the journal. Its proof uses the crown f-polynomial/Chebyshev factorization, ultra-log-concavity and a controlled low-coefficient perturbation. Actual latest theorem/proof and published statement read; no new resolution.
4. Mirzavaziri–Yaqubi, *Latin Eulerian Numbers*, arXiv:2609.25100v1 (19 September2026), Conjecture4.15: strongest remaining target, pursued below. Latest abstract record observed has v1 only. No journal version identified. The companion arXiv:2609.28808v1 was read for the closest cyclic-statistic results, not treated as another candidate.

For each integer n>=3, let T_n(m) count **all labeled** order-n Latin squares with total number of strict vertical adjacent ascents m (sum of column ascents, not cyclic ascents). The exact conjunction is: T_n(m)>0 for every n+1<=m<=(n-1)^2-2; those coefficients form a unimodal sequence; and every such m is attainable by a row permutation of the cyclic square followed by at most one symbol transposition. No claim about the excluded two isolated extreme values is substituted for this target.

## Closest positive prior body: a substantial part is already public

At immutable Omega revision 6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3, read Problems/mirzavaziri-yaqubi-latin-eulerian-multiples.md and actual D5/S3/Combinatorics/LatinEulerian{Defs,Formula,Permutations,Multiples}.lean bodies. Defs.claim is literally: for all n>=5 and 2<=k<=n-3, there exists an order-n Latin square whose column-ascent total is kn. Multiples.result proves that claim by swapped cyclic squares, three explicit permutation families and row reversal. Formula.shiftedSquare_formula is the exact ordinary-ascent/endpoints/unit-difference formula; low_statistics and midpoint_statistics provide the needed permutation statistics. The construction uses the single symbol swap (0,1). Together with original Corollary4.7 it covers the interior attainment/single-transposition clause, not merely a fixed n. Thus neither positivity nor this construction is eligible new credit. The primary dossier explicitly leaves unimodality untreated. No upstream Lean replay or audit of its accepted truth was undertaken.

The source companion's Theorem6.1 and Corollary6.3 concern only row-reordered cyclic squares and their nonzero residue classes. They do not prove the all-Latin-square coefficient inequalities. Exact scope, not a lexical collision, distinguishes the remaining target.

## Independent route A: exact all-square recurrence and stronger inequalities

Normalize the first row to (0,...,n-1) by permuting columns. Every square has a unique normalization, and column permutation preserves total ascents; consequently every normalized coefficient below must be multiplied by n! to recover T_n(m). No symbol relabeling is used in this normalization.

A full exact recurrence retains occupied symbol sets S_c in every column and previous row p. For each permissible next permutation q, disjoint from S_c in column c, update

    F_(r+1)(S_c union {q_c},q;t) += t^(#{c:p_c<q_c}) F_r(S,p;t).

Initialize with first row fixed and exponent zero. After n rows, sum over terminal states. check.py implements this with integer bit masks and exact integer counts; it visits every permitted row extension once. independent.py uses a separate cell-by-cell recursion at n=3,4,5.

At n=6 the normalized counts on m=7,...,23 are

    3,82,521,4462,15806,58354,123230,207182,309678,
    207182,123230,58354,15806,4462,521,82,3.

Total normalized mass is 1128960; multiplying by 720 gives 812851200. The distribution is symmetric and unimodal. The stronger log-concavity invariant already fails at m=9:

    521^2 - 82*4462 = -94443.

Thus a blanket log-concavity or negative-real-rootedness proof of the interior polynomial cannot work. This is not a refutation of source unimodality. Orders3–5 agree with the independent cell recursion and source small data. Order6 is a single exact enumeration, checked for mass and reversal symmetry; it does not have a second independently implemented full enumeration.

**Precise gap in this route:** the recurrence is valid for arbitrary n but there is no proof that its final coefficients increase up to n(n-1)/2. Positivity of transitions does not imply this inequality, and the failed stronger invariant cannot supply it. No claim that this recurrence is a novel theorem.

## Independent route B: cancellation across isotopy orbits

Try to partition Latin squares into row/column/symbol permutation orbits and prove each orbit has symmetric unimodal interior counts. This would suffice for the full target because all symmetry centers coincide. It is false already for the cyclic orbit at n=7.

For symbol permutation s and cyclic-row order p, form the literal square L(i,c)=s((p_i+c) mod n). Put

    w_d(s) = #{x:s(x)<s(x+d mod n)}.

Then its total ascents are the sum of w_(p_(i+1)-p_i mod n)(s) over adjacent row indices. routes.py groups row permutations by exact directed-difference profiles and evaluates this sum. To reduce redundant parameters it fixes p_0=0 and s(0)=0. Row-index translation just permutes columns. Cyclic rotation of symbol VALUES preserves total ascents for any Latin square: each value occurs n-1 times as an upper entry and n-1 times as a lower entry, so wraparound gains and losses cancel. Therefore the full parameter distribution is n^2 times this reduced one. Allowing arbitrary column permutations and then quotienting duplicate squares changes every coefficient by the same positive factor, by constant stabilizer size. Hence these reduced coefficients have the same shape as the actual cyclic isotopy orbit.

At n=7, the reduced parameter count is (6!)^2=518400. Coefficients at m=20,21,22 are 99894,97440,99894: a strict central valley. Another valley is at m=13, with neighboring coefficients 516,408,1512. All these ranks lie in the source interior8..34. independent.py separately constructs each square and directly counts all 42 vertical comparisons, without the difference-profile formula; it reproduces the entire coefficient vector. No estimate or floating-point sign enters.

**Precise gap in this route:** the cyclic isotopy orbit is a proper subset of all order-seven Latin squares. Other orbits can and may fill its valleys. This establishes an obstruction to an orbit-by-orbit proof, not a counterexample to T_7 unimodality. No complete all-Latin-square order-seven count was attempted; its size exceeds this lane's useful bounded experiment scope.

## Strongest objection, falsifier, and disposition

The strongest objection to promotion is decisive: there is no inequality comparing the aggregate T_n coefficients for arbitrary n, and no exact all-square coefficient valley at any n. Existing public work already supplies the attainable-support part. Helpers, a finite confirmation, and a failed stronger conjecture do not resolve Conjecture4.15.

A mathematical falsifier would be n and source-interior a<b<c with T_n(b)<min(T_n(a),T_n(c)), supported by a complete exact enumeration/certificate or ordinary counting proof. A universal proof would need to show symmetry plus T_n(m)<=T_n(m+1) below the midpoint, with positivity/attainment retained from the actual sources. An isotopy-subset valley is explicitly insufficient. Any prior public theorem proving these full aggregate inequalities would independently exclude novelty.

Recommendation: UNRESOLVED; discovery credit0. No PROOF.md, Lean work, paper, acceptance nomination or changed count. Root alone decides acceptance; campaign remains7additional/37total.

## Freshness/access and experiment limits

Inherited registry API403 remains respected. No API request/retry/bypass was made. No usable reset header was available in the inherited r61 evidence inspected. Latest observed Omega head6c27b0a... at15:49 is not represented as current HEAD. Pinned raw primary files were read for concrete subsumption, not as a route around API access controls or proof of current exhaustiveness. Cached actual Lean-tree paths from the polyomino acceptance evidence were used only for triage; Blueprint filenames were not called Lean files. The saved freshness and priority status remains HOLD.

HTTP provenance stores exact URLs, UTC, status, versions and byte hashes. Aaltodoc web fetch returned403; a separately already-launched ordinary repository fetch returned200 and redirected canonically to its public content endpoint. There was no challenge bypass or repeat after receiving an HTTP403 on that transport. pdftotext reported a reconstructable Ai PDF xref warning and a Latin PDF font mismatch; HTML/PDF text agreement was used for the actual statement. No claim of visual journal-typography audit.

All Python and exact experiments use copied capped_run.py: per-child AS512MiB, process-group RSS512MiB, CPU210s, wall230s,40ms sampling, BLAS1. Guard JSON preserves exit, cap failures (none), sampled peak RSS and wall time. bash run.sh reproduces all arithmetic checks without networking. Exact finite checks are evidence only. No browser, account, external contact, git or other-lane edit.
