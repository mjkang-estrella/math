# H019: matched high-memory arithmetic screen for chord bonus

2026-10-08. Status: root/Astra paper derivation; independent Sol algebra,
prefix schedule, recovery and exception checks completed; accepted as a scoped
arithmetic comparison only.
Not a new ECDLP algorithm or a full-runtime benchmark. Improvement **NONE**.
The purpose is to avoid comparing a high-memory proposal only against rho.

Primary source: Galbraith, Wang and Zhang, *Computing elliptic curve discrete
logarithms with improved baby-step giant-step algorithm* (2017),
[published paper, full PDF](https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf).
Astra read the complete paper; root read Lemma3.2, Algorithm2, Lemma4.2 and
the block-overhead discussion. The earlier eprint fetch returned403. The paper
combines paired additions with simultaneous inversions; interleaved negation
BSGS averages (2sqrt(2)/3)sqrt(q) generated points for uniform full-range
scalars, with square-root memory. Its grumpy-giants constant is conjectural and
is not used. The exact Lemma4.2 loop cost has (ell+1) inversions per block;
the subsequent approximate expression omits this factor. We use exact costs.

## Our specialization and accounting

This derivation is a transparent specialization of known block generation,
not a claimed discovery or a constant quoted from the paper. Keep full affine
centers X_j and precompute full affine offsets uT. Emit only x(X_j±uT), because
these side outputs are stored rather than advanced. For d=(x(X_j)-x(uT))^-1,
the two slopes are (y(X_j)±y(uT))*d. Two multiplications and two squares produce
the two abscissae; output ordinates are unnecessary. Center advances still cost
full affine additions. Exceptional denominators and infinity need dispatch.

For k centers and ell pairs per center, each ordinary batch inversion costs
I+3(k-1)M. The ell side rounds and one center round cost

    ell*(I+3(k-1)M+2kM+2kS)
      + (I+3(k-1)M+2kM+kS).

Dividing by k(2ell+1) emitted keys gives

    Cx(k,ell) = S + 5(ell+1)/(2ell+1) M
                  + (ell+1)/(k(2ell+1)) (I-3M).

The limiting arithmetic cost is 2.5M+S, when inversion amortization, setup,
terminal blocks and exceptional cases have been separately controlled below.
This expression omits field additions by convention, and says nothing about
lookup, allocation, labels, memory traffic, branching or actual clock cycles.

To preserve contiguous interleaved prefixes, initialize k centers at index
ell+j*(2ell+1), j=0,...,k-1, and advance all by k*(2ell+1)T after each batch.
Each emitted block is the next contiguous k*(2ell+1) indices. This avoids
silently assuming that arbitrary widely spaced parallel streams preserve the
usual prefix coverage proof. Index labels suffice: a match
x(iG)=x(Q-j*D*G) gives candidates j*D±i modulo q. Verify candidates directly;
no stored side ordinate is required. D is the giant stride, not field cost M.
Retain advanced centers for the next block; do not insert their out-of-prefix
keys early. Their full advancement work is charged to the preceding block.

Finite wrapper checked by Sol: D=ceil(sqrt(2q)); baby and giant index prefixes
through ceil(D/2) cover every scalar by choosing j nearest to d/D and
i=|d-jD|. Infinity is a sentinel with direct scalar recovery. Away from final
wrap seams, prefixes of length L have L(2L-1) signed coverage, not literally
2L². This yields the stated leading average plus O(1) under a uniform scalar
prior; a different input distribution needs its own analysis or paid blinding.
Deterministic full-range coverage does not require that prior. Completing
equal-size prefix blocks costs O(B) extra keys, B=k(2ell+1). Peak tables are
bounded by 2*(ceil(D/2)+1+B) abscissa/index records plus O(k+ell) full-point
and scratch records. Up to two scalar-verification multiplications are paid.

For an arithmetic asymptotic with bounded I/M, choose k and ell growing slowly,
for example polylog(q), with k*ell=o(sqrt(q)); charge initialization and final
overshoot. The cost of special dispatch must also be bounded for the selected
schedule; it is not hidden in an empirical constant. A real finite implementation
must choose finite k,ell and report their exact costs. Square-root storage of
abscissae and indices is essential to this comparator.

Exception count (checked independently by Sol): set W=2ell+1, B=kW<q,
ell>=1. Centers S+(rB+ell+jW)T are distinct while the total index span is
less than q. For each u<=ell, a center can equal uT or -uT at most once each.
Infinity occurs at most once, causing at most ell side-pair dispatches; equality
to ±BT occurs at most twice in center advancement. Thus O(ell) exceptional
dispatches per list cost O(ell*(I+M+S)) with individual full formulas.
This deterministic count needs no mixing assumption. With polylogarithmic
k,ell and bounded I/M, it is lower order than the square-root main term.

## Comparison with the proposed F=3 case

Use s=S/M in [0,1], and ordinary amortized full addition 5M+S as one unit.
Within the stated arithmetic/coverage models, the leading coefficients of
sqrt(q) are

    B = (2sqrt(2)/3)*(2.5+s)/(5+s),
    C = sqrt(pi)/(2sqrt(3))*(7+s)/(5+s).

C assumes the chord schedule earns useful-collision enhancement F=3 over
negation rho; that enhancement itself is unproved. B<C throughout [0,1].
For example at s=.8, B is approximately .536 and C approximately .688.
One can check the inequality without simulation: (7+s)/(2.5+s) decreases
over the interval, with minimum16/7, still exceeding
(2sqrt(2)/3)/(sqrt(pi)/(2sqrt(3))). These are arithmetic estimates, not measured
solver throughput. Source headline constants in different units are not copied.

F=3 alone therefore supplies no supported high-memory material-gain rationale.
This does NOT prove all chord schedules slower in wall time. A surviving
proposal needs a justified larger useful-collision enhancement, a restrictive
memory regime excluding this comparator, or measured table/other overhead large
enough to overturn its arithmetic deficit. Such evidence is currently absent.
No numerical experiment or broader formal infrastructure is admitted by this
screen. Known extra automorphisms must be matched on both sides when applicable.

## Review process

Native Astra /root/h007_additive_relations completed primary-baseline analysis
after its chord review. Root checked paired formulas, exact per-key algebra and
sign recovery against the primary text. Native Sol /root/h010_early_dependencies
confirmed per-key arithmetic, contiguous-prefix repair, finite coverage,
exception bound, scalar recovery and memory wrapper. The brief
explicitly excludes new numerical work, edits, children, and hardware claims.
The broad ECDLP research goal remains open.
