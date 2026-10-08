# H017 SP3: executable detector attempts and Singer-coordinate filters

2026-10-08. Follow-on PAPER algorithm exploration after0bb94aa. Native Astra
/root/h007_additive_relations explored algebraic detectors independently of
native Sol /root/h010_early_dependencies's geometric branch. Root proposed
the Singer-coordinate alternative after the geometric brief, checked Sol's
quotient identities and derived the sparse-output observation below. No numerical
experiment, code, new Lean claim or improved algorithm. The original Grok and
Factory H017 initial briefs remain distinct and have not been given these results.

## Two executable algebraic methods, both above the cost gate

Let n be on the scale q^(1/3), so the target detector cost is o(n^(3/2)),
including failures and extraction. All coordinates are admitted elliptic points;
deduplication retains labels and witnesses and has its own cost.

1. Build C(Z)=product_(z in L3)(Z−z). For each u in L1 build
   R_u(Z)=product_(v in L2) S3(u,v,Z), then gcd(R_u,C). A nonconstant gcd
   detects a third coordinate; a retained product tree or a scan recovers v,
   followed by signs, target-coefficient and scalar verification. Fast polynomial
   arithmetic gives tildeO(n) setup, tildeO(n) per u, tildeO(n²) total field
   operations and tildeO(n) streamed workspace. Even reading all n factors for
   each u already costs n². An expanded simultaneous bivariate product does not
   avoid quadratic representation size. Calling it a resultant supplies no faster
   primitive. This overlaps the earlier product/gcd family; not a new discovery.
2. For square-free split list polynomials A,B,C, the quotient algebra
   Fp[X,Y,Z]/(A(X),B(Y),C(Z)) is a product of field copies on the n³ triples.
   The element H=1−S3^(p−1) is their exact zero indicator. Explicit binary
   powering and tensor polynomial arithmetic take tildeO(n³ log p) field
   operations with n³ dense storage; tensor multipoint evaluation extracts
   witnesses. H=0 proves emptiness, but its FIELD TRACE cannot replace H:
   a nonzero count may vanish modulo p. A short powering DAG is not a bound
   on reduction or zero-testing cost. This overlaps earlier quotient-algebra
   cards and does not justify a new implementation.

These are costs of concrete methods, not lower bounds on every compressed
resultant, quotient or tensor algorithm. Bit work additionally charges field
arithmetic, coefficient representation, labels, comparisons and memory.

## Geometric full-pass slope grouping

Sol's independent geometric attempt uses k slopes chosen uniformly and
independently of the lists. For every slope lambda, compute y−lambda*x for
all signed entries and group matching intercepts across the three lists.
All candidates still need an actual group-equation check: repeated entries
on a line alone do not establish intersection multiplicity or a valid relation.

For q>3 and affine points, a valid signed witness has at most two slopes up
to global negation. A uniform k-element slope subset therefore retains it
with probability at most2k/p. The iid witness expectation O(n³/q) gives

    s_batch <= O(k*n³/(p*q)).

Root checked this union-bound argument and its complete-cost consequence.
The specified full-pass implementation pays Omega(k*n) scan work plus setup
of at least n entries, grouping, failed candidates and verification. Using
both s_batch<=1 and the displayed upper bound, independent fresh retries cost
at least Omega(max(n,p*q/n²)). At n on the scale q^(1/3), constant batch
success would require k=Omega(p). Even optimizing this particular scan
schedule over n gives (p*q)^(1/3)=Theta(q^(2/3)) when p and q are comparable.

This screens uniformly chosen slopes and literal full scans. It does not
cover target-adaptive useful-slope selection, implicit batched incidence,
dependent preprocessing reused across retries, or every geometric detector.
No numerical timing is needed to decide this specified work bound.

## Root's Singer-coordinate alternative and scope

K=Fp³, and K*/Fp* is cyclic of odd order N=p²+p+1. Relative to a fixed
generator, let D be the exponents of the projective line span(1,theta).
It has p+1 elements. SP3 becomes e1+e2+e3 in D, where each admitted e lies
in C=2^(-1)*D, because its projective square lies on that line.

This representation would require paid conversion to exponent coordinates;
finite-field discrete-log algorithms do not automatically give scalar ECDLP
recovery. The screens below even GRANT cheap conversion. No numerical
finite-field DLP cost estimate or guaranteed subexponential solver is adopted.
Sol inspected [Guillevic's NFS-DL paper](https://arxiv.org/pdf/1505.07553),
§§1.2–1.4 and3.1–3.2: field preprocessing and individual booting/descent are
separate paid stages, and smoothness modelling is part of the estimated cost.
That source does not establish a rigorous complete solver for these projective
logs or justify a finite-size negligible-conversion claim.
Building the entire D table costs at least p entries; a dense cyclic transform
over N costs at least N entries. Both exceed the single-target square-root
reference. An implicit detector remains a different, missing operation.

### Literal quotient-membership filters

Sol derived, and root checked, a sharper obstruction to a specific filtering
implementation. For a divisor M of N, let d_r count D in residue class r mod M.
The perfect-difference property gives

    sum_r d_r² = p+N/M,
    |sum_r d_r*exp(2*pi*i*j*r/M)|=sqrt(p)  for j!=0 mod M.

Fourier inversion implies

    d_r >= [p+1−(M−1)*sqrt(p)]/M.

Thus if M−1<(p+1)/sqrt(p), EVERY residue class contains an element of D.
Filtering a triple only by whether its sum lies in the projected support of
D rejects nothing. A dense transform on a larger quotient already costs
Omega(sqrt(p)) entries. Constructing the histogram is itself paid, not free.

This applies to literal support membership in a cyclic quotient M|N. It does
not exclude phase/amplitude sketches, nonhomomorphic partitions, weighted
filters, multiple coupled constraints or all Singer-coordinate algorithms.

### Full sparse convolution still has a quadratic output

Root's exact counting observation is separate from random-exponent heuristics.
Native Sol independently verified it, including the invariant-subspace proof.
D is a perfect difference set: for any nonidentity projective multiplier g,
the two projective lines Lambda and g*Lambda intersect in one point. They
cannot coincide, since a proper2-dimensional subspace stable under an element
g outside Fp would be a module over Fp[g]=K, impossible. Thus each nonzero
cyclic difference has exactly one ordered representation in D. Multiplication
by2 is invertible modulo N, so C=2^(-1)*D has the same property.

For disjoint sets A,B contained in C, each of size n, all n² sums a+b are
different. Indeed a+b=a'+b' with a!=a' gives a−a'=b'−b; uniqueness forces
(a,a')=(b',b), contradicting disjointness. If a=a', then b=b'.
Consequently an algorithm explicitly outputting the full nonnegative convolution
of these two lists must output n² entries. This applies even if exponent
conversion were free. Repeated/overlapping input classes require their own
bookkeeping; the claim is deliberately for disjoint deduplicated lists.
For iid affine elliptic-point lists, each admitted projective class has mass
2/(q−1). A union bound gives probability at most binomial(3n,2)*2/(q−1)
of any class duplicate across the lists. At n on the scale q^(1/3) this is
o(1), so conditioning disjointness loses only o(1) from the earlier constant
witness-success bound. This observation does not manufacture a detector.

Root read the introduction/abstract of [Jin–Xu, Shaving Logs via Large Sieve
Inequality](https://arxiv.org/pdf/2403.20326), whose nonnegative sparse-convolution
bound is in OUTPUT sparsity. Substituting the input size n for that parameter
would be wrong here. Their theorem does not claim to find only an intersection
with an implicit D while avoiding the other outputs. No general convolution
or implicit-intersection lower bound is inferred.

## Decision

None of these specified operations supplies the required detector. Preserve
the exact screens without extending them to all finite-field or coordinate
algorithms. A concrete implicit intersection/localization operation with paid
empty-instance handling and witness recovery could still change the decision.
No prototype, larger experiment or generic formal infrastructure is justified
by the present constructions. Verified improvement remains NONE.

Validation: independent native paper attempts and root cross-checks as credited
above; no runtime experiment. `./scripts/check.sh >
/tmp/ecdlp-h017-detector-check.log 2>&1` exited0 from dlp-research, all363 existing
dependency audits passing. Those checks do not formalize these paper results;
no new Lean claim or Audit.lean change was made.
