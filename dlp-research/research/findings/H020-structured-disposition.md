# H020 structured relation proposals: missing detector, corrected scope

2026-10-08. Verified improvement **NONE**. No experiment admitted.
Claude Opus's independent report is retained in H020-structured-opus-raw.md.
Native Astra /root/h007_additive_relations completed independent review; root
checked the algebra and explicit comparator below. Exact original task handle
and followup brief are in hypotheses/H020-independent-candidates.md. This is
paper analysis, not Lean verification or a new impossibility theorem.

## Higher-order Cauchy structure is real, but the proposed detector is absent

For disjoint distinct u_i,v_j, define K_ij=(u_i-v_j)^(-2) and
Delta(K)=diag(u)K-K diag(v). Then Delta(K)_ij=(u_i-v_j)^(-1), a nonsingular
Cauchy matrix for square lists. Ordinary bounded displacement rank does NOT
follow. Instead Delta²(K)=11^T. For M_ij=S3(u_i,v_j,w)/(u_i-v_j)²,
Delta²(M)_ij=S3(u_i,v_j,w) has rank at most three, since its degree in u is
at most two. This is higher-order structure, not the ordinary claim in the raw
report. Coincident coordinates require separate dispatch.

Fast matrix-vector multiplication is plausible for a concrete reason: the
squared-Cauchy action is minus the derivative of the rational function
sum_j z_j/(X-v_j), evaluated at the u_i. Product/remainder trees implement this
with fast polynomial arithmetic. But a zero ENTRY is not a zero matrix-vector
product. Entrywise reciprocals such as sum_ij 1/(w-S_ij) are nonlinear
functionals whose construction is not supplied. The raw floating-precision
objection is invalid for exact finite-field arithmetic. Neither a detector nor
a detector lower bound has been established.

## Triple progressions: a fully specified square-root comparator

Take n>=1 and A_i=A0+iR, B_j=B0+jS, C_k=C0+kT with indices 0<=i,j,k<n, seeking
A_i+B_j+C_k=Q. Let h=ceil(sqrt(n)), m=floor(n/h), t=n-hm. Split the complete
middle-index blocks as j=j0+h*j1 with 0<=j0<h and 0<=j1<m. Construct

    U_(i,j0)=iR+j0S,
    V_(j1,k)=h*j1*S+kT.

Match U against Q-A0-B0-C0-V in a dictionary. Lists have nh and mn entries;
successive group additions generate them, with indices retained for recovery.
Duplicates may share a representative for this membership problem. For the
remaining t<h values j=hm,...,n-1, use one dictionary of iR and scan all k
against Q-A0-B0-C0-jS-kT. This tail costs O(nt+n) group work and O(n) storage.
Thus ALL valid middle indices, empty instances and witness recovery cost
O(n^(3/2)) group operations/storage, plus dictionary comparisons or expected
hashing and setup. The explicit tail avoids returning an invalid padded index.

At n~q^(1/3), this is a square-root upper bound. It is NOT a lower bound on
other detectors. For direct target Q and lists with known scalar labels relative
to G, any valid witness gives its scalar sum. More general affine-in-Q relation
lists need a nonzero target coefficient: this membership routine alone does
not guarantee a useful ECDLP relation or free enumeration of all witnesses.

Coverage depends on the steps. A common step gives only O(n) possible sums.
Mixed-radix steps R=G, S=nG, T=n²G give all n³ integer sums before reduction
modulo q. Cyclicity does not make these short-list coverages equivalent.

The actual [square-root Vélu theorem](https://arxiv.org/pdf/2003.10118),
Theorem4.11 and Example4.13, evaluates a structured product at one argument
given an index system; algebra extensions incur size-dependent cost. Astra and
root inspected these primary statements. They do not assert compounded savings
across three arbitrary progression directions. No cheaper triple-AP operation
was supplied here.

## Composition, multiplicity and transposition

Kedlaya–Umans composition needs actual input polynomials f,g,h and computes
f(g) modulo h. The raw report constructs neither those inputs nor a join or
witness reduction. Its runtime quotation also suppresses the computational
model: the [primary abstract](https://drops.dagstuhl.de/entities/document/10.4230/DagSemProc.08381.5)
states near-linear bit complexity with field-size dependence. The reviewer
accessed primary abstracts but full-PDF attempts failed; extra theorem
hypotheses are not accepted from memory.

With cross-list abscissae distinct, the unreduced product of pair quadratics has
degree exactly 2ab, regardless of repeated roots. Small distinct support does
not lower this degree without a separately constructed radical or membership
representation. Conversely high degree is not a runtime lower bound for an
implicit evaluator. Coefficient-to-value evaluation is linear; constructing
coefficients from point lists is nonlinear. Transposition does not construct
the missing representation. Empty-instance detection need not universally
read n² objects. Freiman-type structure does not prove a square-root runtime
lower bound either. These overbroad closures are rejected.

## Next gate

A survivor must specify an operation below n^(3/2), including input construction,
denominators, empty-instance detection, coverage and useful witness recovery.
The explicit balanced comparator above makes that gate concrete. No current
card crosses it, and no general family of coordinate-aware methods is closed.
Other independent H020 lenses remain live; no broad infrastructure or numerical
sweep follows from these negative findings.
