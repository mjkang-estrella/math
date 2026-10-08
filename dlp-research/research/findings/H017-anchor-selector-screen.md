# H017: two explicit anchor selectors and the adaptive-selection gap

2026-10-08. Paper derivations, no numerical experiment or new Lean claim.
Verified improvement NONE. Native Astra /root/h006_structured_relation_ideas
delivered partial constructions; its final turn FAILED with a provider
cybersecurity-risk flag. No completed final report is claimed and no retry was
made. Root checked the partial formulas; separate native Astra
/root/h007_additive_relations reviewed signs, counting scope and exceptions.

Setup and admitted fibres are as in H016-fiber-boundary-screen.md: p>3,
E(Fp)=<G> of prime order q>3, Q=kG nonzero, and known numerical-log anchors.
Colour0 rows sum to O; colour1 rows sum to3Q. Only distinct rational triples
at finite function values enter the two-row constructions below. Slopes may
be chosen for each attempt; all arithmetic, rejected attempts and storage cost.

## 1. Two anchors on each row

Choose a colour0 chord through A_i,A_j. Its third point is
U=−A_i−A_j. Choose a colour1 chord through B_r−Q,B_s−Q and translate
back; its third point is V=3Q−B_r−B_s. Hence

    U=V  iff  3Q=(B_r+B_s)−(A_i+A_j).

The proposer's first partial message had the opposite sign; root flagged it,
the proposer explicitly corrected it, and the independent reviewer confirmed.
Numerical anchor logs recover k directly from the displayed equation; verify
kG=Q. Quadratic factoring provides no additional information here.

Let S0,S1 be FIXED allowed pair-sum sets, independent of k, of cardinalities
M0,M1. Since multiplication by3 is invertible modulo q, successful admitted
closures cover at most M0*M1 secrets. For uniform nonzero k, the closure success
probability is at most min(1,M0*M1/(q−1)). Target-dependent chord slopes do not
change this equation when the allowed sum sets are fixed.

For the particular implementation that materializes those entire fixed sets
before receiving Q, constant success requires M0*M1=Omega(q), hence
M0+M1=Omega(sqrt(q)). Writing all entries already costs that many word operations,
before constructing points, finding a difference, verifying or handling failures.
This is a charged single-target setup screen, not a multi-target amortization
lower bound. A competent matched baseline must include its own preprocessing.

**Independent review correction:** fixed anchor pools do not make a
target-adaptively selected subset of pair sums secret-independent. The bound
uses the full fixed allowed sets, NOT merely the sums actually computed.
A hypothetical cheap implicit selector could choose just the useful pairs for
each Q. The counting argument does not exclude it. No such operation or
favorable complete-work estimate was supplied. Likewise, table cardinality
alone imposes no materialization cost on an implicit/compressed representation.

## 2. Reconnect two unknown endpoints

Start with an admitted colour1 row {A,U,V}, where A is a known anchor and
U,V are unknown. Thus A+U+V=3Q. The colour0 chord through U,V has third point

    W=−U−V=A−3Q.

The two rows share both unknown points. If W is a known anchor they close:
R=2,E=2,H=2,c=1 gives F=R+2−2c−H=0 in H016's incidence accounting.
This is a legitimate parallel-edge closure, but testing W in a known-log
dictionary is exactly testing A−3Q. Factoring fibres is unnecessary to perform
that test. Changing the colour1 slope cannot change W for fixed A,Q.
For fixed allowed anchor sets K0,K1, coverage is bounded by
|K0|*|K1|/(q−1). The same fixed-set versus adaptive-selector distinction applies.

## Exceptions and limitations

These bounds concern the admitted two-row closures. They are not a bound on
a solver that ALSO exploits exceptional chord cases. For example B_r=Q is
a direct known-log hit, a vertical translated pair gives2Q=B_r+B_s, and a
repeated third point can give3Q=2B_r+B_s or B_r+2B_s. If used, such branches
need their own candidate-set union and paid tests; treating them only as failures
would omit potential successes. Infinity/pole, vertical, tangent and repeated-
point cases must be detected. The scoped constructions reject inadmissible
triples; no full solver with exception handling was implemented.

These are two explicit operations, not a proof against growing dictionaries,
larger components, coordinate-dependent selection, compressed pair sets or all
ECDLP algorithms. They show why implementing a fibre engine around these
particular closures adds no established advantage over direct group/dictionary
operations. Next useful evidence would be an actual cheaper selector for useful
boundary relations, with its preprocessing, success probability, extraction,
memory and final scalar recovery charged. No prototype justified yet.

Validation: paper identities checked by root and the separate reviewer. The
repository command `./scripts/check.sh > /tmp/ecdlp-h017-operator-check.log 2>&1`
exited0, with363 existing dependency audits passing. These identities are not
new Lean-audited claims; no theorem or Audit.lean change was made.
