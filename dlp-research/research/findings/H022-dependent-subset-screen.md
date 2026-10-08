# H022 list-dependent subset: exact bridge, missing index

2026-10-08. Native Astra /root/h007_additive_relations initial constructive
role COMPLETED; root checked the identities and conditional expectation.
Brief in hypotheses/H022-independent-candidates.md. No edits/runs/children
by the proposer. No numerical experiment or Lean claim. Improvement NONE.

Allow the subset itself to depend on the indexed list: S=B+D, with each
generator list of length n. This has a compact description and at most n²
distinct points, the intended subset scale when n is about q^(1/3).
The exact translation query is

    P+B_i in S  iff  exists j,k, P=B_j-B_i+D_k.

For numerical logs b_i,d_k and P=alpha*G+Q, a verified triple recovers
the target scalar b_j-b_i+d_k-alpha modulo q. The recovery bridge is real;
it does not construct the needed output-sensitive reporting operation.

The literal pair-dictionary implementation enumerates n² sums before queries
and stores at most n² distinct keys, with duplicate witnesses handled. That
enumeration costs too much for the proposed softO(q^(1/3)) construction and
already exceeds the square-root comparator at n about q^(1/3). This is the
cost of this implementation only: structured sets, compressed indexes and
other ways to produce distinct sums require separate analysis.

Retaining only B,D instead leaves the displayed correlated three-list search.
For uniform P independent of B,D, the exact conditional expected number of
reported indices is n*|S|/q, since each P+B_i is uniform. A small output
expectation does not pay for locating those indices.

Two earlier results cannot be applied without new proofs: H021's fixed-subset
four-independent-list second moment assumes a different independence pattern;
its iid three-list reduction does not automatically apply to B,-B,D. No
impossibility or new conditional hardness assertion is inferred here.

The remaining constructions in this pass duplicated existing missing
primitives: scalar intervals require unknown scalar translation; a cheap
coordinate membership test does not supply translate enumeration; a compact
divisor product does not itself give an intersection finder. No new positive
gain mechanism or prior-art distinction emerged. Do not count a repeated
range oracle as another candidate.

Reopening requires an explicit paid triple-reporting/index operation with a
favorable setup/query/memory ledger and justified success. No benchmark of an
undefined operation or broad formal infrastructure is justified. The other
H022 EDS and independent full-solver roles remain separate live work.
