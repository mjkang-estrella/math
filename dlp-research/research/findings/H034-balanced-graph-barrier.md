# H034 restricted graph setup versus duplicate-equation barrier

Status: paper analysis under explicit restrictions, independent Astra review
completed. No experiment, Lean proof, novelty claim or universal ECDLP lower bound.
The main square-root exponent and verified-improvement status NONE are unchanged.

This concerns the named signed-pair construction with a uniform full-range input scalar (including0) and eager independent
uniform label pairs in Fq² on n vertices of a simple bipartite graph. For t inspected keys, m=t/2
edges have been considered, up to one partial edge. Take a fixed cap A*sqrt(q),
q^(1/4)=o(n), n=o(q^(1/3)), and require maximum degree at EVERY capped prefix
Delta=O(sqrt(q)/n), with constants independent of q. No adaptive graph choices,
helper-point detectors, free labels, learned advice or additional recovery oracle
are included. Startup seed events and geometry-first recovery retain the prior
H034 contract. The finite frozen diagnostic does not use or test this result.

## Elementary supersaturation calculation

At a prefix with bipartition sizes a,b, a+b=n, let K=choose(a,2) and let
S=sum over right vertices choose(degree,2). Counting common-neighbor pairs,

    S >= m²/(2b)-m/2,
    C4 = sum over left pairs choose(codegree,2)
       >= (S²/K-S)/2.

For m>=2b and m²>=8bK, S>=m²/(4b)>=2K, so

    C4 >= S²/(4K) >= m⁴/(64b²K) >= m⁴/(2n⁴).

Empty/one-vertex sides cannot meet these dense-prefix hypotheses. Root initially
used the weaker m²>=4bK, which gives only S>=K and does NOT justify S²/(4K).
The independent reviewer caught this finite-constant mistake. The repaired
condition is automatic asymptotically on each fixed positive t/sqrt(q) window,
since m²/n³ tends to infinity. No finite-size constant is silently reused.

Distinct four-support equations satisfy the previously reviewed exact identity
N=8(D-C4), where D=choose(m,2)-sum_v choose(deg(v),2). Thus N<=4m² everywhere,
and on any fixed positive window below the cap,

    4m²-N >= 8*C4 = Omega(q²/n⁴).

Dividing by q loses Omega(q/n⁴) of the ideal birthday-event intensity. Intensity
alone is not a stopping-time lower bound; the next paragraph is essential.

## Why the restricted stopping bridge can work

Under the degree bound, the AGG zero-event error and additional lower-support
collision probability are uniformly O(m*Delta/q)=O(1/n). The proof and primary
AGG source are in H034-paired-sum-mathematical-screen.md; this is a new use of
that bound, not a claim of mutual independence of pairwise-independent events.
Startup seed exceptions cost O(n²/q) in probability; the full-range Q=O
direct shortcut costs O(1/q), absorbed here. Both are smaller than the
positive-window intensity gap q/n⁴:

    (1/n)/(q/n⁴)=n³/q -> 0,
    (n²/q)/(q/n⁴)=n⁶/q² -> 0.

Since q/n⁴ tends to zero, the four-support survival on such a window exceeds
exp(-t²/q) by Omega(q/n⁴). Outside that window, N<=4m² gives survival at least
the ideal tail minus the same error. Integrating the entire fixed cap therefore
cannot cancel the positive window contribution. The independently reviewed
stopped-key result is

    E[min(T,A sqrt(q))]
      >= sqrt(q)*integral_0^A exp(-x²)dx + Omega(q^(3/2)/n⁴).

Rounding/partial-edge O(1) terms are smaller in this regime. Startup termination
must be charged in the error, not treated as conditioning that preserves IID.
A general graph with Delta as large as n lacks the needed error separation;
this analysis does not exclude such graphs or different detectors.

## Cost interpretation and limits

Under a common fixed positive cost per inspected key and paid eager setup at
least proportional to n, this gives a restricted additive-overhead surrogate
Omega(n+q^(3/2)/n⁴), whose balanced power is n=q^(3/10). It matches the exponent
of the thickened-incidence construction up to logarithms in its stated upper
bounds. It does NOT prove complete-work optimality: iterator prices, table
traffic, allocation, exact randomness, arithmetic and backend costs differ.
The ideal capped birthday reference is not itself an implemented baseline.
No gain over H019 or competent rho follows from optimizing this remainder.

For a fresh independently blinded fallback with uniform-input expected cost
F(q)=O(sqrt(q)), use the SAME exact fallback mean in the ideal reference:

    sqrt(q)*integral_0^A exp(-x²)dx + F(q)*exp(-A²).

Here all terms use a common cost unit (or multiply the key integral and gap by
the common key price). The cap-probability error adds at most
O(F(q)*(1/n+n²/q)), smaller than the established gap. Thus it cannot cancel
the penalty. This is the independently reviewed finite-cap qualification; it
keeps the entire fallback remainder in both sides. Do not replace an unspecified
o(sqrt(q)) remainder by O(q^(3/10)), or compare unequal success criteria.

Process: root proposed the barrier and derived the graph inequality; native
Astra /root/h007_additive_relations independently identified the degree-balanced
bridge and corrected the finite supersaturation constant. Read-only paper work,
no runs/imports/edits/children by reviewer. Root alone integrates.

Validation: `./dlp-research/scripts/check.sh > /tmp/ecdlp-h034-graph-barrier-check.log 2>&1`
from the repository root: exit0,366 existing dependency audits. No Lean claim/Audit addition. Checks do
not prove the paper theorem or execute the frozen diagnostic. The restriction
and independent review, rather than check count, support the stated conclusion.
