# Analytic discovery r130: PREFREEZE, no nominee

Author: Myeongjin Kang (no affiliation). Original exposition CC BY 4.0; original code MIT.
Runner provenance: Factory Droid / claude-opus-5-5 / high. Upstream pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb;
theorems at the pin are stipulated true. This report assigns no gate, verdict or count.

## Outcome

No exact scope was frozen and nothing is nominated. Two families were screened in depth; neither yielded a
result that is both full-scope provable here and carries an identifiable unpaid nonroutine operation.

## Family 072 (Brennan's conjecture; strict inverse-first-power companion)

Zero-count family in the stale navigation counts. Both papers' source bodies were acquired at the pin and
authenticated (Git blob SHA-1 and size against the complete preprint tree); the operative sections were read in full.

**General-exponent screen (S1, author derivation, not proved to packet standard).** Running the printed
Brennan/companion mechanism with weight |F'|^{-s}, s in (0,2) (t = -s), only the exponents move:
- the transfer exponent beta = log_2 rho must exceed s-1, which holds whenever beta >= s^2/4 since
  s^2/4 - (s-1) = (s/2-1)^2;
- the eigen-law moments are E a = -beta/s and E|q|^2 = beta(beta+1)/s^2;
- the potential exponent is k = (beta+s+1)/(s+2), and the escape and covering steps need only s > 0;
- the averaged Jacobian factors as s^2 (s+2)^2 k^2 E J = (4 beta - s^2)(beta + s + 1);
- at beta = s^2/4, k = (s+2)/4 lies in (1/2,1), so |q| >= 1-k > 0 and the companion's harmonic barrier applies
  with log(1/(1-k)) in place of log 4.

This indicates B(t) < t^2/4 on all of (-2,0). Every step is a printed proof with a parameter left free, and the
factorisation is the only new computation. By the campaign's lesson on parameter substitutions this is technical,
so it was not frozen.

**Positive exponents t in (0, 6-4sqrt2).** Under the same mechanism the moments, Jacobian sign and period
condition survive. Two steps fail: the area tail of the escape lemma diverges for t >= 0, and k = (2-t)/4 < 1/2 makes
the real-axis covering sum diverge. Repairing the second step would need a new statement: under the eigen-law,
the set of bad boundary targets has zero area almost surely. No argument for it was found.

**Primary literature preempts the direction.** arXiv:2610.23853v1 (Binder, Ivrii, Prause, Smirnov, 16 Oct 2026)
states B_b(t) <= t^2/4 on [-2,2], strictly on ]-2,2[ \ {0}, and hence B(t) < t^2/4 on ]-2, 6-4sqrt2[ \ {0}.
Its written proof is deterministic (index-theorem signed area for the potential s^k/|f-xi|), covers the
non-strict inequality, and bypasses both failures above. It uses the same potential exponent as S1. Strictness
is announced, with details deferred to a separate paper. A project-history search found no earlier record of this
note.

**Remaining gap (PREFREEZE).** A complete proof of strictness, B_b(t) < t^2/4 for t in (0,2), needs a
quantitative excess of maxima over saddles in the signed-area inequality, that is, a barrier with averaging valid
at positive exponents. I have no argument for it. Its novelty is also limited, because experts have already
announced the result.

## Family 213 (no percolation at criticality on quasi-transitive graphs)

All 11 source files were acquired and authenticated; the main file and introduction were read. The natural
extension, site percolation on every quasi-transitive graph, would need the full proof to be rerun. The two-cluster
bound across an edge has no site analogue, because adjacent open sites always share a cluster, and no black-box
site-to-bond reduction is available. The extension was dropped as infeasible in one round.

## Avoided, per brief

Sources 331, 090, 262, 143/T143D45, 087, 097, 372 (Lamé); the r128 auxiliary gap; T191V56 (Heilbronn);
structural distance-coloring 158; combinatorial, topological, arithmetic and algebraic families; the active rounds
fresh-arithmetic-discovery-r97 and fresh-structural-discovery-r133, which were not read.
