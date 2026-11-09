# Candidate 325519: literal Conjecture 4.2 refutation

Status: research candidate, zero accepted credit. Independent novelty, significance and statement-fidelity review and a paper remain for the parent. No public action requested or performed.

## Source and scope

Dias da Silva–Freitas, arXiv:1305.1139v1, submitted 6 May 2013, Section 4, defines r_k as the minimum number of spectral radii among k-element positive sets and asserts, for **every** positive (k−1)-element B, that adjoining zero produces fewer than r_k. The primary full HTML body was read, including the entire final section and the preceding construction proof. The normalized MathDB 325519 matches this clause: B is not assumed to be an extremizer. Source notation has an extraneous parenthesis, with no semantic effect. Journal version: European Journal of Combinatorics 34(8), November 2013, pp.1316–1325, DOI 10.1016/j.ejc.2013.05.014. The author page links to ScienceDirect. DOI fetch returns a redirect HTML; direct journal fetch returns 403, not a paper. No retry or bypass. Published-version changes therefore remain a review gap.

This is a k=5 witness refuting the universal statement, not a proof of an isolated true parameter case, not a k=1/domain loophole, and not a determination of r_5. No use is made of unproved Conjecture 4.1.

## Exact ordinary proof

For a nonnegative 2×2 real matrix with entries a,b,c,d in row order, put s=a+d and D=(a−d)^2+4bc. Its complex characteristic equation is

    (z−a)(z−d)−bc = (z−(s+√D)/2)(z−(s−√D)/2)=0.

Thus both eigenvalues are real. Since s≥0, the plus root is nonnegative and dominates the absolute value of the minus root. The spectral radius is consequently (s+√D)/2. This argument includes reducible matrices and zeros: no unjustified irreducible Perron assumption is needed.

Enumerate the 625 matrices over each alphabet A={1,2,4,8,16} and C={0,2,3,5,7}. Encode a radius by (s,D). If D is a perfect square, replace this pair by (s+√D,0). This replacement preserves its real value, by the nonnegative square-root identity. The A enumeration has 115 normalized keys, so it has at most 115 actual radii. The C enumeration has 118 keys.

It remains to prove the latter keys give distinct real numbers; different formal radicals alone are not evidence. For keys (s,D),(t,E), equality of their values implies

    √D−√E=t−s,
    D−E−(t−s)^2=2(t−s)√E.

If s=t, equality forces D=E. Otherwise it forces

    (D−E−(t−s)^2)^2 = 4(t−s)^2 E.

The checker tests the negation of this necessary equation for every unequal pair of C keys (or tests D≠E when s=t). Every test passes by kernel evaluation of integer arithmetic. The generic `incompatible_sound` theorem derives actual real inequality; it does not assume that formal keys are injective. Consequently |Ω₂(C)|=118 and r_5≤|Ω₂(A)|≤115. With B={2,3,5,7}, Conjecture 4.2 would give 118<r_5≤115, contradiction.

## Route progression and certificate

A first diagnostic compared zero-adjoined geometric progressions with positive geometric progressions for k=3,...,8; they do not refute the claim. That does not test arbitrary B. The surviving route uses non-geometric prime alphabets; the bounded exact k=3,...,10 comparison finds the k=5 witness above. No inference of truth or novelty is made from this finite diagnostic. The final proof checks just two 625-element enumerations, perfect-square normalization and pair separation, with proved soundness, not a blind search.

`generate.py` independently regenerates `diagnostic.json` with all 118 representatives. It also regenerates the finite arithmetic module (but is not needed by the verifier). `Spectral.lean` proves normalization and separation soundness and the exact finite certificates using `decide +kernel`. `Semantics.lean` defines the radius as the supremum of complex characteristic-root norms, proves the quadratic formula and dominance, and proves the actual 2×2 matrix determinant bridge. `Endpoint.lean` proves equality between the enumeration and source Ω for natural alphabets cast into the reals, defines r_k using the natural-number infimum over **all finite positive real alphabets**, and proves

    SpectralExclusion.source_conjecture_refuted : ¬SourceConjecture.

No conjecture is encoded as an assumption of a supposedly complete result. All source bridges are proved. The source endpoint is not merely the arithmetic key comparison. The sole `SourceConjecture` hypothesis occurs under negation in the refutation proof.

## Bounded novelty screen

Fresh current GitHub head was retrieved successfully: 4eaee87548250b2682affda7d05d947c05554bae, commit date 2026-10-30T00:35:35Z, unchanged from recent review metadata. The cached full preprints tree at that head was searched for spectral-radii/positive-entry/partition/hyperstar paths. A fresh pinned overview body was read/searched for Freitas, spectral radii, integer partitions and hyperstar: no relevant entry. The path regex also yielded unrelated Positive-Metric-Entropy paths; these do not clear a target. Palomar revision 651 query `spectral radii` returned one unrelated Mahler/compositum result; the partition and hyperstar queries returned no entries. These bounded queries do not exhaust the registry bodies.

Web searches included the exact source title with counterexample/conjecture, the literal Conjecture 4.2 phrase with spectral radii, MathDB ID 325519, the author names, and site:github.com/openai/math with spectral radii. Located sources include the primary arXiv paper, author publication list, University of Lisbon publication metadata and the 2012 precursor cited by Johnson et al. No full matching refutation was located. This is **not** proof of novelty; no MathSciNet/zbMATH/citer-complete screen or global unreviewed claim is made. Current MathDB body is not retrieved (historical access denial inherited); corpus is immutable evidence, not current solution status.

Prior-campaign ledgers for all 39 credited results and current new-twenty ledger were read. None of their credited endpoint families is the spectral-alphabet exclusion conjecture. A bounded old-note navigation (depth/size/exclusion limits retained in script history and JSON) found inventory/tag/routing hits, no substantive old target dossier. That is not global clearance.

# Selected route 325293: excluded by primary public proof

The primary Conjecture 3.1 in 1304.1315v3 was read. Trying to extend the hyperstar leaf equations to any cored hypergraph does not force a common center: odd loose paths allow the same equality. The companion Hu–Qi–Shao paper, *Cored hypergraphs, power hypergraphs and their Laplacian H-eigenvalues*, explicitly proves this before the present campaign. Its actual Propositions 4.1 and 4.2 and proof bodies were read in the author-hosted published PDF (source receipt/hash retained). Proposition 4.2 states lambda(L)=2 for odd-uniform loose paths of length at least three, and the maximum degree is two. Such a path is connected but not a hyperstar. The proof rules out lambda>2 by alternating signs along nonzero core blocks; zero core coordinates are handled by propagation from the endpoints. It explicitly concludes the earlier conjecture has a negative answer. This is not a new discovery; stop. Formalizing it earns zero credit.

# Selected partition route 325436/325438: excluded by exact prior constructions

Borg's 1304.6563v1 definitions and Conjectures 1.1,1.2,2.1,2.2 were read. Fixed-length integer partitions are sorted positive tuples, but intersection means equal values anywhere, not matching positions. A largest-star injection for all k,n fails; the related same-coordinate theorem cannot substitute for it. A natural complete-intersection construction takes partitions containing at least t+1 distinct values from [t+2]. It is t-intersecting by the pigeonhole principle. Deleting those prescribed parts and correcting multiple counting gives

    sum_(i=1)^(t+2) p(n−S+i,k−t−1) − (t+1)p(n−S,k−t−2),
    S=(t+2)(t+3)/2.

This route is already public: Person–Schweser, arXiv:2610.01747v1 (1 October 2026), Theorems 1.2/5.2 and Lemma 5.1, with proof bodies read. It gives 620>618 for P_(31,8) at t=1 and asymptotic counterexamples at all intersection scales. Its introduction also records the earlier four-family in P_(8,3), versus a three-element star, and the 2016 amended exception. Both fixed-length targets therefore earn zero. The unrestricted-length targets 325435/325437 and distinct-part 325439 are not automatically resolved: comparison with a star in one layer does not bound the total family across all lengths. Those routes remain parked rather than counted by analogy.
