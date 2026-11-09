# Source target and exact reduction; unresolved ordinary proof

Let m be a positive integer and let a1,a2,a3,a4,K be integers in [0,m-1]. Entries are indexed and may coincide. Put
S = sum_{j=0}^K sum_{T subset {1,2,3,4}} (-1)^(4-|T|) floor((j+sum_{i in T}ai)/m).
The target is S >= -3 floor(m/3), for ALL these parameters, with no parity or divisibility restriction.

Literal source: Thanatipanonda–Wong, JIS21 (2018), Article18.1.8, Section4 pp14–15; the independent sentence 'We conjecture the lower bound' on p15 gives this inequality. Table1 p2 also lists it. It is consequently not an invented fragment of Conjecture17. The latter, pp16–17, has additional all-n extremizer and recurrence assertions; its n4 example assumes m multiple3. No full-C17 resolution is asserted here. The source writes sets, but its repeated-entry extremizers and the 2017 predecessor's explicit multiset Definition1 settle the intended indexed convention. The subset sign is positive for sizes0,2,4 and negative for sizes1,3; the empty subset is included.

Chronology: Onphaeng–Pongsriiam received Sept28 2016, published Jan14 2017; Thanatipanonda–Wong arXiv v1 Aug10 2017, v2 Feb14 2018, JIS published Feb23 2018. The live JIS PDF retrieved Oct30 2026 has the same SHA256 as the r237 original. All hashes are in scientificbindings.json and retrieval.jsonl.

Nearest proof actually read: Onphaeng–Pongsriiam, Article17.3.6, Definition1 p2 and Theorem9 proof pp15–19. It expresses the alternating subset sum through signed two-variable Jacobsthal blocks and applies 0<=S2<=floor(m/2). Its general conclusion is -2^(ell-2)floor(m/2)<=S_ell<=2^(ell-2)floor(m/2); sharp lower/upper witnesses use respectively odd/even ell AND even m, all entries m/2, K=m/2-1. It does not establish the requested even-ell lower bound. Wong Theorem15 p15 combines two- and three-variable bounds to give only -2floor(m/2)-floor(m/3). Wong Theorem16 records the predecessor's parity sharpness with m even, not a new proof of our target.

## Exact quotient/remainder route
Write H=K+1, so 1<=H<=m. For each subset let s=sum ai=qm+r with 0<=r<m. Directly splitting j=0,...,H-1 at j=m-r proves
F(s)=sum_j floor((j+s)/m)=Hq+max(0,r+H-m).
Thus S is the signed sum of these sixteen F(s). This includes equality at r+H=m and H=m. It loses no residue term.

There is also a quotient-free formula. Since 0<=j+s<5m, count the thresholds lm, l=1,...,4. With C_H(u)=max(0,min(H,u)), exactly C_H(s+H-lm) of the integers j in [0,H-1] satisfy j+s>=lm. Therefore
F(s)=sum_{l=1}^4 C_H(s+H-lm).
The equality is integral, including s=0, H=1,m and all threshold boundaries. Each floor is nonnegative here, so threshold counting has no negative-level correction. Both formulas were compared exactly against the defining sum for every sorted tuple and every K through m=24.

This gives a finite piecewise linear INTEGER formulation, not a continuous approximation. Introduce integer t>=0 with 3t<=m<=3t+2; then t=floor(m/3). The counterexample condition is the finite sum of 64 clipped linear terms < -3t. Sorted a1<=a2<=a3<=a4 is valid: permuting the four labels bijects all subsets and preserves their signs and sums. No complement or rotation reduction is used in the solver.

all-m-query.smt2 encodes precisely these constraints. Z3 5.3.3 returns UNSAT, both in the default run and a separate proof-producing run. z3-proof.sexpr is an emitted solver proof object. It has NOT been independently checked and has NOT been converted to an ordinary proof. This computational conclusion is a strong lead, not a certified resolution, novelty claim, or eligible credit. A small independent exact checker or an ordinary chamber/Farkas argument remains necessary. Do not infer acceptance from the .sexpr extension or the UNSAT result.

## Cyclic cancellation route
For n>=2, changing any entry ai by m changes each affected floor by1; the signed sum of those constants is (1-1)^(n-1)=0. Also sum_{j=0}^{m-1}floor((j+s)/m)=s for nonnegative integer s, since s=qm+r gives mq+r=s. Alternating the linear s over subsets proves a full period sums to0 for n>=2.

Let bar ai=(-ai mod m). Before canonical reduction take m-ai, which may equal m. The integer identity floor((-x-1)/m)=-floor(x/m)-1 gives f_{m-a}(m-1-j)=-f_a(j); the |T| and constant corrections cancel in the subset sum. Consequently S_bar_a(m-2-K)=S_a(K) for 0<=K<=m-2. K=m-1 separately gives0. Thus any complement reduction must transform K too. Arbitrary starting-index rotations do not preserve a prefix sum, so none is asserted.

Finally f4(j)=f3(j+a4)-f3(j), by splitting subsets according to membership of4. Hence S4 is the difference of two cyclic interval sums of f3 of length H. This proves cancellation but the existing separate interval bounds do not yield the requested residue-sensitive estimate. No sign-run classification has been proved. The solver formulation is the stronger next route, provided its certificate can be checked independently.

## Prior scope
Immediate current-batch SUMMARY/SCOUTING/discovery alias screen found the exact floor family only in r237. Current arXiv title, author/floor, and Jacobsthal/Tverberg queries return the original 1708.03190v2 only. This is not an exhaustive citing search or public-registry clearance. Previously denied GitHub raw/API/codeload/diff/patch and other blocked historical intervals are parked, with no retry, browser, proxy or TLS bypass. No worldwide priority assertion. Counts remain9/39/next40; root alone decides.
