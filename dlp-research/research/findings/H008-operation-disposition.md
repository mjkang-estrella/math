# H008: explicit operations fail their full-cost gates

Status: paper derivations and scoped rejection, not Lean theorems or numerical
experiments. Verified improvement NONE; ordinary prime-field prime-order ECDLP's
working classical square-root reference remains unchanged. Native Astra roles
/root/h007_additive_relations and /root/h007_lattice_carries independently supplied
operations after H007's corrected specifications. Root integrates their results.
No solver package, new engine, benchmark or formal infrastructure was built.

## Dictionary pair-divisor translation

Given known-log points Pi=aiG, build all signed sums of two distinct dictionary
entries. Retain exact point keys, scalar labels, indices and all witnesses when
deduplicating. This costs O(B²) group operations and retained witness records.
For each R=Q+uG, scan pair points A and look up R-A. Compatible disjoint pairs
yield the four-root relation and k=sum(signed ai)-u; verify kG=Q. An overlapping
pair also solves DLP if accepted by the broader solver, though not the frozen
four-distinct-indices predicate. Exhaustion handles empty queries.

With P(T) the product over distinct pair abscissae modulo negation, degree D,
an equivalent representation uses K_R(T)=Res_X(P(X),S3(X,T,x(R))) and gcd(P,K_R).
Known translated points and a product tree construct K_R directly. Usually its
degree is 2D. Exceptional x(R) already in the pair set supplies a known-log answer
directly; all extracted signs and indices still require checks. This is the
established summation-polynomial relation, not a new elimination theorem.

For the accepted sparse random dictionary model D=Theta(B²). Explicit K_R
construction writes Omega(B²) coefficients. Paid pair scanning similarly costs
Theta(B²) for an exhausted query. With the earlier coverage/restart assumptions,
the intended work ledger is ~O(B²+q/B²): q^(3/5) at B=q^(1/5), optimized to
square-root work and pair storage at B=q^(1/4). It misses the chosen per-target
B^(3/2) threshold. Polynomial arithmetic does not improve this exponent.

Root qualification: retaining all witnesses is essential to exact disjoint-pair
emptiness. Arbitrary collision multiplicities can add extraction work; the
report's O(B²) complete-query upper bound is not accepted universally for that
restricted predicate. One may charge all witness combinations, or analyze paid
rejection/rebuilding of dictionaries with nontrivial pair collisions. This only
worsens the present rejection. The sparse-model ledger is not an all-input bound.

Materializing T target polynomials costs Omega(TB²) coefficient writes. A full
target resolvent with Theta(B^4) distinct covered points has that many abscissa
roots up to a constant sign factor, exceeding the B^(5/2) setup gate when expanded.
An implicit nested resultant or companion matrix verifies proposed roots but
does not yet supply fast selection or empty-query detection. These statements
reject the named explicit implementations, not every implicit solver.

## GRR reverse traversal and exact endpoint recognition

Use the frozen H007-grr-v1 chart, B=2^k dividing p-1, V=u+mu_B, full odd prime
curve order, finite R=(r,s), C(x)=x³+ax+b. For a supplied monic degree-five h
whose roots lie in V, set F=(x-r)h. Enumerate at most32 y orientations. Require
nonzero square C at roots; at a repeated root r the orientation is -s under the
gcd(h,D)=1 policy. Hensel lift Y²=C modulo each factor of F and combine by CRT,
including Y(r)=-s. Solve A+YD=0 modulo F linearly in c2,c1,d1,d0, substituting
the frozen c0. Verify A²-CD²=F, gcd(h,D)=1 and the actual oriented point sum.
Constant degree makes each endpoint check polynomial in log p, including paid
finite-field square-root extraction. Two normalized functions with these six
zeros differ by a function with pole order at most five, so a fixed orientation
has at most one solution. This is a paper primitive; simple sign/group checks
already recognized known tuples cheaply. It supplies no reduction in tuple count.

The proposed exact pruning predicate starts P0(X)=S6(u+X1,...,u+X5,r) and defines

    P[j+1](T1²,...,T5²) = product_{eps in {+1,-1}^5} P[j](eps*T).

The product is even in every variable. Start at level k with five ones, reject
nonzero predicates, otherwise traverse square-root child multisets, and run
the endpoint recognizer at leaves. Multiplicity is retained. There are
choose(B+4,5)=Theta(B^5) possible unordered leaves.

Two actual implementations fail before experimentation:

- Dense unreduced pushforward expansion: for a nonzero specialized P0 of positive
  degree delta in one variable, degrees satisfy delta[j+1]=16delta[j]. The32
  nonzero leading coefficients multiply in an integral domain, then replacing
  T² by X halves degree. At level k this is delta*B^4. A dense representation
  has Omega(B^4) slots, exceeding both the target and setup gates. Degree alone
  is NOT a sparse term-count or arithmetic-circuit lower bound.
- Literal recursive product evaluation: T(j)=32T(j-1)+O(32), giving Theta(B^5)
  leaf calls on targets where all leaf predicates are nonzero. Unordered
  memoization preserves this exponent. This is an empty-target worst-case cost;
  a probability/average-cost theorem requires a distribution of such targets,
  not merely their possibility. The literal full evaluator pays this regardless;
  short-circuit variants need their own honest distributional analysis.

Squarefree reduction, subgroup-ideal reduction, sparse circuits or another
witness-producing solver remain open. No claim excludes them. Neither a cheap
endpoint recognizer nor four principal unknowns proves a cheap whole inverse
tree. No generic algebra engine or pilot is justified by these two operations.

Primary context already inspected by proposer and H007 reviewers:
[PKM, sections3.1–3.3](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf),
[Semaev](https://eprint.iacr.org/2004/031). These supply membership/decomposition
context; the recognizer and scoped cost arguments above are research derivations.

## Completed Grok geometry report: independently checked correction

Raw report retained in H007-grok-geometry-raw.md; no favorable claim adopted.
The Hankel card switches from a coordinate-dependent +G/+Q walk to a fixed-G
rational window without justification or a valid shared Somos identity.
A degree upper bound gives an image-size lower bound, not the upper bound needed
to claim q/w effective states. Moreover w*sqrt(q/w)=sqrt(qw) field operations
already loses before any useful-collision filtering. Distinct segments do not
guarantee nonzero scalar-recovery coefficient. Root's stronger fixed-G objection:
normalized raw first rows retain x(P+G)/x(P), a nonconstant rational function of
degree at most4, hence bounded fibers independent of w. Native Astra
/root/h007_lattice_carries independently confirmed this, with the following
important qualification now adopted by root.

The numerator has a double pole at -G; the denominator has no pole there. If
x(G)=0 its zero increases that pole rather than cancelling it. Thus the ratio
is nonconstant. Its pole degree is at most4, from the translated double pole
and at most two denominator zeros. Equal normalized rows preserve the ratio
where the first two entries are not both zero. The simultaneous-zero exception
has at most two points and cannot share such a key with a nonzero pair.
Appending extra raw coordinates cannot enlarge a fiber. Raw finite keys therefore
have at most four preimages, not growing Theta(w) fibers.

A raw window has O(w) undefined locations, NOT a constant exceptional set.
For the natural projective first-row extension, 2<=w<q, poles -jG extend to
distinct coordinate-unit keys. For w>=4, a finite row cannot equal one of these:
it would need at least three distinct zeros of x, whose zero divisor has degree2.
Small w also has bounded fibers. The combined first/last-row/bracket key lacks
a specified pole treatment; it must handle those O(w) locations explicitly or
define an extension. The fixed-G proof does not analyze the mixed +G/+Q walk.
This rejects the delivered raw-row growing-fiber explanation and stated work
gain, not every differently compressed window key.

The independent-label U+V=2S repair pays L² pair work with heuristic L³/q hits,
thus q^(2/3) at L=q^(1/3); a faster reporter is absent. Negation-only x hits need
both signs in coefficient extraction. The doubling/translation card is a rho
variant with no mechanism supporting a smaller state count; its Legendre
evaluation and additions are paid. A single finite-size success or failure
cannot establish or refute an asymptotic claim, contrary to the raw falsifier
wording. No experiment authorized from these cards.

## Next conclusion-changing work

Inspect the actual selection algorithm in Mahalanobis's new
[2607.09814v2](https://arxiv.org/abs/2607.09814v2), independently reviewing
probability conditioning and complete work. Abstract/version verified: v2 dated
2026-08-06; attempted v3 HTML returned404 and was not used. Earlier minor critiques
are evidence to compare, not a substitute for reading this new method. Independent
recent-primary-mechanism search runs alongside it. No improvement accepted.

Validation: no code or Lean claim changed. Exact command
`./scripts/check.sh > /tmp/ecdlp-h008-paper-check.log 2>&1` passed exit0, retaining
363 existing audits. Staged Markdown paths/diff inspected before commit. No numerical test,
seed or runtime is fabricated; all work above is symbolic analysis/source review.
