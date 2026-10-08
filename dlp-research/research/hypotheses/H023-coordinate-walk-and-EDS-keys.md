# H023 concrete coordinate operations and independent reviews

2026-10-08. Two distinct native initial roles completed. Root checked basic
algebra; independent cross-reviews RUNNING before acceptance. No experiments,
edits or children by delegates; root sole integration. Native root+2 fits4;
original H022 Grok broad creative role remains live on its existing handle.
Neither card is a verified complete-solver improvement. Broad ideation remains
active; these are concrete operations rather than another free-oracle card.

## A: fixed-difference low-memory walk (Astra proposer)

For E:y²=x³+A*x+B, G=(g,yG), use u=x(P)-g,v=x(P-G)-g, with explicit
infinity/singular-formula dispatch. The ordered pair identifies P; swapping
implements P->G-P, label(a,b)->(1-a,-b). Canonical sorting gives about q/2
states, unlike the earlier arbitrary two-point state. Whole-pair equality is
the coalescence key; equality of one coordinate is insufficient.

Let c1=2(3g²+A), c2=4yG². Proposed +G update is

    z=(c1+c2/u)/u-v,
    new state=sorted(z,u).

Literal cost2M+I plus additions; batching n denominators gives
5M+(I-3M)/n per update, with no S. This is a possible small kernel saving
against competent negation rho5M+S, not a proved walk saving.

Translation alone has a concrete defect: with u<=v, next minimum cannot
increase. If z>u, the next canonical representative is -P and the next
translation returns to the same reflection class with cancelling labels.
More generally ±G-only choices live on a quotient path and have cycles of
length at most2, apart from explicitly handled boundaries. These claims are
under independent review, not a universal coordinate-walk obstruction.

A mixed operation can double P by computing x(2P) and x(P+(P-G)) with
known difference G. Direct affine xDBL costs2M+2S+I and differential xADD
costs3M+S+I; total5M+3S+2I. If actual expensive-step fraction is rho, the
combined denominator batch gives

    5M+rho*(6M+3S)+(I-3M)/n.

Assuming the SAME useful collision constant as negation rho, arithmetic
saving needs rho<s/(6+3s),s=S/M. At s=.8, even10% arithmetic saving needs
rho<.0262 before hashes, labels, scratch, endpoints, dispatch and escape costs.
No appropriate stopping/mixing law or cheap deterministic escape rule is
provided. State count and marginal uniformity do not prove that law.

Independent reviewer /root/h010_early_dependencies (Sol), RUNNING. Brief:
audit injectivity/reflection labels/coalescence, exact formulas and finite
costs, exceptional known-point recovery, quotient path/cycle claim, actual
branch frequency, matched active-state/scratch memory and DP discovery. Check
primary short-Weierstrass formulas where needed. Decide whether a SPECIFIED
mixing/escape rule has a credible gain, otherwise retain missing assumption.
No runs, edits, children, global lower bounds or experiments yet.

## B: exact EDS match refinement (Sol proposer)

Use h(P)=phi(P)/alpha, alpha=phi(G), p>3,q>3 prime and q not dividing p-1.
For nonzero P,T in the subgroup, normalized division-polynomial identities
give D_T/C=phi(T)²*(x(T)-x(P)), where

    C=h(P)², D_T=h(P-T)*h(P+T),
    N_T=x(T)*C-phi(T)^(-2)*D_T=C*x(P).

Thus (h(P),N_T) should identify the point, and (canonical±h(P),N_T) its
negation class, independent of neighbor spacing G versus DG. Oddness and
nonzero center resolve the sign ambiguity. Derive the phi(T)² normalization
factor explicitly; do not assume neighbor quotients invariant under scaling.

Computing N from available neighbors costs3M+S and no per-key inversion;
fixed inverses, neighbor generation/access, two-field records, indexing and
boundary lookahead are paid. Center zero uses an identity sentinel/direct
target recovery; P=±T makes one neighbor zero without invalidating the formula.

An alternative refines only raw central-key matches by checking

    (x(T1)-x(T2))*C = phi(T1)^(-2)*D_T1 - phi(T2)^(-2)*D_T2,

at5M+S from retained neighbors. A secondary exact N dictionary pays known
refinement once and target refinement once per occupied raw bucket, avoiding
a scan of every raw fiber. Scalar multiplication is then needed only for a
winning recovered scalar, not automatically for every false central-key hit.
This correctness/cost primitive does not rescue already losing EDS kernels.

For fixed nonzero known records P_i and J fixed Q-independent shifts,
uniform Q gives signed raw false-record expectation
(2J/q)*sum_i(c(h(P_i))-1), where c(z)=#{P:h(P)=z}. Correlations do not alter
this fixed-length expectation; stopped-query counts need separate arguments.
No random-function or small-fiber bound is established. Duplicate records
and distinct scalar candidates must be distinguished.

Independent reviewer /root/h007_additive_relations (Astra), RUNNING. Brief:
verify normalization/exponent2, general spacing, signs/zeros/injectivity,
operation counts with paid neighbors, exact secondary-index costs and
fixed-length expectation conditions. Use consistent Liao–Zhang Eq3/5/6;
do not turn a source-normalization issue into an erratum campaign. No edits,
runs, children, experiment or generic formalization. Paper review sufficient.

## Ranking and next gate

A is a speculative material low-memory saving only if an inexpensive escaping
walk retains the competent useful-collision rate; freeze that operation before
testing. B is a concrete supporting matcher, not a new attack or asymptotic
gain; any future EDS candidate must include its extra fields and arithmetic.
Independent H022 Grok may supply unrelated mechanisms. No new benchmark,
hardware rate, proof infrastructure or full-size hardness claim is made.

Delivery update: independent Astra matcher review COMPLETED. Root checked
H023-exact-EDS-matcher.md, including spacing-independent normalization,
sign/zero cases, paid neighbor lookahead, exact secondary indexing and
fixed-length expectation limits. No small-fiber assumption needed for the
exact-key implementation. This corrects mandatory-SCM-per-false-hit claims,
not the unfavorable underlying kernel ledger. Sol walk review remains live.

Final completion: Sol walk review also COMPLETED. H023-fixed-difference-walk.md
records the exact state/translation bridge, memoryless pure-step obstruction,
and the distinct ledgers for hash-before-arithmetic versus paid trial-and-escape.
Both initial roles and cross-reviews complete; no numerical experiment admitted.
Original H022 Grok broad role is the remaining live independent investigation.
