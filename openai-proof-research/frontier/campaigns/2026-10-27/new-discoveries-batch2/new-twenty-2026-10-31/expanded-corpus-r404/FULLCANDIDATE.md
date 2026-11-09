# 349070: full ordinary proof, zero accepted credit

This is a mathematical candidate only. Novelty and significance are NOT qualified; no formal execution, independent review, dispatch or acceptance occurred. The campaign stays 55/60 beyond39,94total. The elementary form of the proof is a reason to examine prior subsumption carefully, not a proved exclusion and not evidence of significance.

## Literal endpoint and primary reading
For every finite connected simple undirected graph with adjacency matrix A, every strictly positive real vector x, put B=A+I and y_i=x_i/(Bx)_i. Then y^T B y <= ||y||_1. This is exactly the preserved record349070 and Guigues, arXiv:2012.07764v1 (14 December2020), Conjecture8.1, equation19, page24. Read the actual statement, normalization definitions, and appendix proof of the conditional Theorem8.1 (page31). The saved unversioned PDF identifies itself as v1. The displayed oslash is componentwise division, not matrix inverse. Connectedness is included in the endpoint although unnecessary for the inequality. No claim is made about convergence of the entire weight vector.

## Proof, every finite size
Let I be the finite vertex set. Write s_i=sum_j B_ij x_j. Since B_ii=1 and all B_ij>=0, s_i>=x_i>0. Hence every division below is legitimate and y_i>0. Symmetry gives B_ij=B_ji.

Expand the finite double sum
 D=(1/2)sum_{i,j} B_ij x_i x_j (1/s_i-1/s_j)^2.
Every summand is nonnegative. The first square term sums to
 sum_{i,j} B_ij x_i x_j/s_i^2
 =sum_i (x_i/s_i^2)sum_j B_ij x_j
 =sum_i x_i/s_i.
The second square term has exactly the same sum by exchanging i,j and using symmetry. The cross term is
 sum_{i,j} B_ij x_i x_j/(s_i s_j)=sum_{i,j} B_ij y_i y_j=y^T B y.
Consequently
 ||y||_1-y^T B y = D >=0,
as required. For an empty finite index set both sides and D vanish; for n=1 the same computation applies. No graph program, search over instances, numerical evaluation or formal checker was used.

## Independent ordinary reformulation and equality audit
Put W_ij=B_ij x_i x_j and d_i=sum_j W_ij=x_i s_i. W is a symmetric nonnegative weighted adjacency matrix. For f_i=1/s_i, the expression D is the finite Dirichlet form sum_i d_i f_i^2-sum_ij W_ij f_i f_j. Expanding it directly gives the same identity. This is a second algebraic audit, not independent agent review and not a literature novelty result.

For a connected graph on a nonempty vertex set, equality holds iff s is constant. Indeed, a zero sum of nonnegative terms forces 1/s_i=1/s_j on each edge since x_i x_j>0. Connectedness propagates this equality along any path. Conversely constant s makes D zero. If s_i=c for every i, then By=B(x/c)=s/c=1, so N(y)=y. Conversely N(y)=y and y>0 implies By=1, hence y^TBy=sum y and equality. Thus equality corresponds to N(x) already being fixed; it does not require x itself fixed. For example, for the one-vertex graph x=2 has N(x)=1 fixed but x is not fixed. This audits an overstrong strictness sentence in the source's surrounding theorem; it is not a new creditable endpoint correction.

An exact two-step increment supplies a further check. Set t_i=(By)_i>0 and z=N(y). Then
 sum_i(z_i-y_i)=sum_i y_i(1-t_i)/t_i
 =sum_i y_i(1-t_i)+sum_i y_i(1-t_i)^2/t_i
 =D+sum_i y_i(1-t_i)^2/t_i>=0.
This proves monotonicity from the first normalized iterate, with equality iff y is fixed. All normalized entries are <=1, so the sequence of their sums from iterate1 onward is bounded and nondecreasing. This is only a consequence of the exact target, no separate candidate or credit. It does not prove componentwise convergence.

## Qualification and contrary assessment
Three native search calls/nine strings were exhausted across the lane; the exact queries and complete responses are persisted. Two calls included Guigues or the exact Conjecture8.1, and one searched specific current public registry domains. No verified exact public proof was obtained from those responses. That observation is NOT novelty evidence. Four current registry root bodies were fetched with all20 IDs charged. Their heads are in inventories.json; no source tree was traversed or proved absent. A 2026 search hit mentions further Guigues graph-normalization work without supplying a sufficiently identified exact applicable theorem; its body was not acquired. The source's cited approximation and matrix-normalization literature has not been fully checked. No claim of worldwide or repository-wide clearance is made.

The proof is a standard symmetric Dirichlet-form expansion. A reviewer may judge the exact application a routine corollary. No complete earlier-to-target theorem bridge has been verified here, so I neither claim qualifying novelty nor manufacture a routine-exclusion verdict. Significance is unresolved, with a serious objection that this may be below the campaign threshold. No mathematical lemma in the displayed ordinary proof remains unpaid. The unpaid gates are prior/subsumption investigation, significance judgment, literal Lean implementation and source bridges, independent review, strict extracted replay, paper and root acceptance. The dormant plan is not authorization to execute.
