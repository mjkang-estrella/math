# Metric edit costs: prefreeze comparisons

The examined full question was the following, without freezing it. Given an arbitrary finite metric alphabet Sigma together with a gap symbol bottom, suppose that this alphabet metric embeds into L1 with distortion D. Is the metric edit distance on ALL words of length at most n embeddable into L1 with distortion

    D exp(C sqrt(log(2n) log log(4n)))

for an absolute C independent of alphabet size, n, every gap/substitution cost ratio, and the minimum positive cost? Insertions/deletions cost d(a,bottom), substitutions cost d(a,b). One common map and scale must handle every pair, including the empty word. No such full theorem was assembled; no target was frozen. This note supplies neither an aspect-ratio-dependent replacement nominee nor a full-target impossibility claim.

## What is already operative in source099

The actual circle companion, *Finite Circle Obstructions, Binary Codes, and Histogram Embeddings for Edit Distance* (September27,2026), `upper.tex`, was read in full. The proof represents a finite L1 metric as a finite cut combination, Poisson-samples those cuts at rate alpha, and uses the expected L1 distance between cell-count histograms of overlapping windows. Collision probability is exactly exp(-alpha rho). The lower estimate uses all cross-window distances, and the upper estimate uses a chosen partial pairing plus unmatched windows. Both are available operations, not just an existence theorem for an unspecified map. The complete `preliminaries.tex` and `assembly.tex` were also read during preselection; their LCS identities concern the source's ordinary unit costs.

Ostrovsky–Rabani's actual author-hosted preliminary paper (August19,2005), Lemma8 and the proof of Theorem7, was read at the histogram/recursive construction. This is an explicit primary ancestor of the window architecture. The author PDF is not silently identified with the final2007 journal version. The lower-level Lemma6 and the final remainder of the paper were not read in full here.

Actual structuralr40 `operation-ledger.md` and `report.md` credit the whole architecture and all three pinned companions. Its frozen full target is distortion depending on a DISTANCE cap K rather than the LENGTH cap n; its periodic alignment gap is different. Its report also explicitly records weighted-edit conventions among technical screens. Actual structuralr58 `report.md` concerns cyclic edit distance. Neither target is restarted.

## Equal gap costs leave a compatible route

These calculations test the strongest existing reduction; they are not a proposed narrower theorem. Normalize every gap cost to1 and allow any symbol metric with d(a,b)<=2. The alphabet L1 map supplies the recursion's base with expansion D. The source's lower window test does not need a positive minimum substitution cost:

* For a block distance k>=2, choose a dyadic s at most (k+2)/3. The source's deletion comparison gives every cross-window distance at least k-2(s-1)>=s, and s is a fixed fraction of k. Its histogram lower estimate therefore applies unchanged.
* For 0<k<2, use s=1. There is one whole-block window. Its expected histogram distance is 2(1-exp(-alpha rho)), which is bounded below by a fixed multiple of k when rho>=k and alpha has the source's fixed lower bound. Thus small substitutions do not require extra scales down to the minimum alphabet distance.

A substitution of cost delta affects at most s windows at a given scale, each by edit cost at most delta. The partial-pairing estimate gives expansion at most 2s alpha E_child delta, with s alpha the existing scale budget. A paired deletion/insertion move has cost2 and admits the same shifted matching of windows as in the source: nonexceptional blocks have s-1 exactly paired windows, with only the boundary windows unpaired. Any equal-length alignment can be realized by substitutions on surviving matched positions and paired deletion/insertion moves; the usual recurrence remains of the form

    E_n <= C log^2(2n) (B + E_child).

With base expansion D>=1 this has the same subpolynomial length dependence, multiplied by D. These are checks of compatibility, not a separate standalone embedding manuscript or independently reviewed theorem.

For variable lengths, pad by a fresh star with d(star,a)=1. This extends the equal-gap alphabet metric because d(a,b)<=2. Erasing stars projects each padded edit to an original edit of no larger cost. Conversely, realize an original optimal alignment without exceeding the maximum endpoint length; after each insertion/deletion, adjust the tail stars. This costs at most twice the original gap edit and leaves substitutions unchanged. A factor-two comparison suffices; the exact LCS padding identity for unit costs is NOT asserted for arbitrary metric substitutions. No literal use of that identity is a new proof step.

## Arbitrary gap costs: the primary repairs more than a naive grid

Let g(a)=d(a,bottom). Then |g(a)-g(b)|<=d(a,b)<=g(a)+g(b). For an alignment, matching a with b saves

    w(a,b)=g(a)+g(b)-d(a,b),  0<=w(a,b)<=2 min(g(a),g(b)).

Mader–Tavasoli–Wang arXiv:2609.14873v1, actual Sections3,6 and7 at the extents in the reading log, supplies the following compatible operations. This is the same stronger primary already credited in structuralr112, whose `screen-121.md` was read before treating a raw-index obstruction as a new gap.

1. For each threshold t, clipped prefix mass uses g_t(a)=min(g(a),t). Every edit changes the difference of the two clipped prefix masses by at most its ORIGINAL cost (Lemma3.1).
2. At mesh s=epsilon*t/64, mark BOTH adjacent cuts of every symbol with clipped cost>s, then greedily group only the light-symbol runs. This gives O(n) cuts, with at most3+2|I|/s in a clipped-mass interval I (Lemma7.1). Inward snapping never crosses a heavy symbol and deletes original mass less than4s in total. Merely saying clipped mass does not control true deletion cost would miss this repair.
3. If one side has at most d characters, discarding matches involving gap costs at most H=epsilon*t/d loses at most2epsilon*t, because there are at most d matched pairs. The simplified distance retains the original deletion/insertion cost of discarded characters (Lemma6.2). It is not edit distance solely on retained strings.
4. Composing two monotone matchings through a common d-character string retains at most d pairs. The metric triangle inequality gives the exact original-cost bound in Lemma6.4, hence Corollary6.5's feasible dense-box label with additive about2t overhead.
5. Canonical nonempty snapped windows stay inside their original windows and remain ordered across different thresholds. Empty anchors need not remain ordered across thresholds; the primary explicitly omits them from the chain and charges their actual masses. Lemma7.3 supplies membership and acceptance of canonical tags with its fixed slack.

These are stronger than a pointwise mass heuristic. The primary uses pair-dependent optimal subpaths, one short-string window partition, a guessed distance scale and candidate tags. Its threshold count is logarithmic in the number of windows/precision, not the global cost aspect ratio.

## Exact unresolved interface

The fixed-index source upper bound for moving one symbol charges unmatched window boundaries at unit scale. With arbitrary gaps, rotating a cheap symbol a across a long heavy word has edit cost at most2g(a), arbitrarily small. This invalidates that unchanged unit charge as an original-cost estimate; it does not rule out mass-sensitive maps. The primary's clipped/heavy construction above is the strongest actual repair examined.

To finish the full question, one would need a common embedding architecture on the entire word space whose feature choices are independent of the comparison partner, which retains a lower all-cross-window separation mechanism AND a summed upper bound proportional to the original cost of every edit, through every recursive level and all cost scales without aspect-ratio loss. Pairwise feasible boxes and threshold-specific inward snapping do not yet give that common map. Replacing all symbols by runs proportional to their costs introduces an expanded LENGTH depending on cost ratios; it does not establish the desired original-length bound. No assertion that every alternative construction fails is made.

Structuralr112's exact unclosed target is a near-linear approximation algorithm using simultaneous lazy refinements, not the present embedding question. Its existing heavy-symbol and common-center calculations are credited, not renamed as r128 results. We did not produce a complete new arbitrary-gap invariant, and therefore did not freeze this question or promote the compatible equal-gap calculations.
