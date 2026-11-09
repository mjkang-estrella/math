# Sustained ordinary investigations; zero accepted credit

## 343192: complete ordinary construction proof, public counterpart
Scope: integers n>m>1, k=n-m, a=m(k+1)/n nonintegral, A=ceil(a); indices [o]={0,...,o-1}, as explicitly fixed on p7 of original arXiv1907.04844v4. Original edges from u_i go to ceil(im/n)+alpha mod m, 0<=alpha<A. This indexing matters; no one-based reinterpretation is silently imposed. k-critical means after deleting ANY k vertices of U a perfect matching remains, hence after deleting at most k vertices there is a matching saturating V.

Initial shortcut: minimum degree k+1 on V alone does not imply robustness; several V vertices could share all neighbors. Degree balance is likewise insufficient (the new paper's Section4 explicitly distinguishes it). The original biregular proof Theorem5.5 uses an integrality relation and is not a proof of the nonintegral claim. I recovered its printed pp15-17 after the first full extraction display truncated in the middle; pp15-16 were separately read, p17 present in initial display. That route cannot simply reuse its integer d.

Full alternative: define h_j=floor(jn/m), j=0,...,m-1, and give v_j the k+1 U-neighbors h_j-beta modulo n, 0<=beta<=k. The h_j are distinct, since n/m>1, and k+1<n because m>1. This smaller graph is contained in the proposed graph. Indeed, write jn=mh_j+gamma, 0<=gamma<m. For t=h_j-beta in Z (before reduction modulo n),
ceil(tm/n)=j-floor((gamma+beta*m)/n).
Set alpha=floor((gamma+beta*m)/n). Then alpha>=0 and
alpha<=floor((m-1+km)/n)=floor(a-1/n)<=ceil(a)-1.
The last inequality holds also for integral a (then floor(a-1/n)=a-1). Replacing t by its representative i modulo n changes ceil(tm/n) by a multiple of m; hence the same alpha gives the desired edge modulo m. This pays the wraparound bridge rather than assuming it.

Let S be a nonempty subset of V, s=|S|, and H={h_j:v_j in S} inside Z/n. Its smaller-graph neighborhood is H-{0,...,k}. A nonempty proper subset T of Z/n satisfies |T union (T-1)|>=|T|+1: otherwise T-1=T, and iteration of the generator -1 forces T=Z/n. Applying this successively k times yields
|H-{0,...,k}|>=min(n,s+k)=s+k,
since s<=m=n-k. Delete any k vertices D of U. Then |N(S) minus D|>=s for every S, including empty S trivially. Finite Hall supplies a V-saturating matching, perfect when exactly k vertices were removed. For fewer removed vertices the same Hall inequality holds directly. Extra edges preserve this matching. All source hypotheses paid; no search, enumeration, calculation program, or numerical check used. No unproved mathematical bridge remains in this ordinary argument apart from the standard finite Hall theorem, here invoked explicitly.

Primary/public bridge: original Conjecture6.1 p18 is exactly the reserved construction. Published Cichacz-Gorlich-Suchan, Opuscula Math46(2)(2026),201-218, DOI10.7494/OpMath.202602181: Construction2.4 and Conjecture2.5 p205 reproduce it; Lemma3.5 pp207-208 proves smaller graph inclusion; Theorem3.6 pp208-209 proves criticality; Corollary3.7 p209 concludes the conjecture for every nonintegral a. I read the actual proof pages, not just abstract. The smaller graph uses exactly h_j-beta and same zero-based indices. Journal page gives received2025-03-14, revised2025-12-20, accepted2026-02-18, online2026-04-10. arXiv2307.07315 was located in search with 2023 date but its body/version was not acquired, so no claim about its original version's exact contents. The journal's proven scope predates this lane and its August2026 MathDB creation; it postdates the 2019 conjecture. These chronologies are distinct.

Contrary assessment: replacing their induction with cyclic-set growth may be a cleaner proof, but it still proves precisely the already public universal claim. No new construction, stronger fault model, or uncredited exact MathDB solution survives. Zero credit is due to the complete public scope bridge, not shortness or Hall alone. No formal dispatch, acceptance, paper, or novelty clearance.

## 342704: full literal counterexample; definition correction, zero credit
Literal f(k) is the greatest power-of-two divisor. Take m=4,n=8 and Gamma=(Z/2)^5. Its order32=mn is even, exponent r=2, f(4)=4,f(8)=8,gcd=4,lcm=8. Thus literal 2r min(...)=16>=8. Nevertheless no distance magic bijection exists.

Direct ordinary obstruction, independent of any computed witness: write L(i,j) for the label, coordinates modulo4 and8. Equal weights at (i,j+1) and (i-1,j+2) cancel the two common neighbor labels and imply
L(i,j)+L(i+1,j+1)=L(i-2,j+2)+L(i-1,j+3).
Because -2=2 modulo4, on the main diagonal x_t=L(t mod4,t mod8), the pair sums s_t=x_t+x_(t+1) obey s_t=s_(t+2). In characteristic2,
x_0+x_4=s_0+s_1+s_2+s_3=0,
so x_0=x_4. But the two vertices are (0,0) and (0,4), distinct. This contradicts injectivity. Four distinct neighbors exist at every vertex for these parameters; cancellation uses the abelian group law, and characteristic2 is literal in Gamma. This refutes the iff by one valid instance, without needing necessity over all other parameters.

Initial temptation to construct a labeling from the record's inequality fails by the pair-sum obstruction. Sustained source comparison: the primary paper defines f(m)=m/4 if4|m, m/2 ifm=2 mod4, m ifodd (p9), not the power-of-two divisor. Its Theorem3.1 pp9-11 proves nonexistence by diagonal pair-sum recurrence and exponent; Theorem3.6 p15 gives nonexistence on C_(2^a) square C_(2^b) for a!=b>=2. Substituting a=2,b=3 gives exactly the witness. Conjecture4.1 p16 uses that source f. With source f, 2r*min(1,2,4)=4<8, so no contradiction to the source conjecture exists. The record has also omitted m,n>=3 from cycle definitions; the witness satisfies that stronger restriction and uses no endpoint loophole. The acquired PDF marks arXiv1905.04946v1 13May2019 but includes a November27,2024 title-page date. No publication-version equivalence is assumed from that anomaly. The theorem/proof is present in the actual acquired bytes, predating this investigation. The current search surfaced later classification claims, but their bodies were NOT read and do NOT support any additional exclusion.

Contrary assessment: an exact literal refutation is mathematically valid, yet all of its content is already in Theorem3.6, and the novelty is only fixing a corrupted definition. Zero credit by a complete public bridge and source-correction precedent. Not a novel ordinary survivor; no dormant formal dispatch warranted.

## 343074: sustained full-scope mechanism, precise incomplete lemma
Literal scope: all positive integers m<n, n>3; u in size-m part, v in size-n part; strict ept(u)>ept(v), including m=1. Primary arXiv1906.11083v1, pp1-2 defines each oriented blue-to-white attempt independent, probability |N[blue] intersect B|/degree; synchronous old blue state. Section2.3 pp9-10 gives Proposition2.5 and Conjecture2.6 with exactly this scope. Theorem2.2 p4 proof read: a transient Markov resolvent yields expectation. Tables do not prove the universal inequality; no table values have been recomputed.

For state (a,b), a blue in size-m part, b in size-n part, define
p_A=1-(1-(a+1)/m)^b, p_B=1-(1-(b+1)/n)^a.
The increments X~Bin(m-a,p_A),Y~Bin(n-b,p_B) are independent: they involve disjoint oriented attempts and distinct targets. If no white targets remain on a side its increment is zero, so a base outside [0,1] never needs evaluation. Set T(m,n)=0 and T(a,b)=expected remaining rounds. For any other reachable nonempty state,
(1-P00)T(a,b)=1+sum_((x,y)!=(0,0))Pxy*T(a+x,b+y).
Here Pxy is the product of the two binomial probabilities. This is an exact finite triangular recurrence, not an algorithm run in this lane. Finiteness: with any nonempty nonfull blue set in connected K_m,n there is a positive-probability force across a blue-white edge; repeated state progress over finitely many levels bounds expectation by a finite sum of geometric means. The conjecture is the strict inequality T(1,0)-T(0,1)>0.

Route1, direct monotone coupling: coordinatewise blue-set inclusion implies faster completion on the SAME graph by using shared independent uniform attempts and monotonic force probabilities. The singleton states here are incomparable under inclusion. Swapping coordinates swaps part sizes and denominators too; it does not give a coupling with ordered rates. The mean first-round number of new blues is 1 from either seed, so mean reproduction alone has no strict ordering. A rate claim based just on degree ignores multiple attempts and the closed-neighborhood +1.

Route2, exact renewal after the first cross-part force: define q_d=1-(1-1/d)^d, w_d(j)=binom(d,j)(1/d)^j(1-1/d)^(d-j)/q_d for1<=j<=d (d=1 defined directly). Then
T(1,0)=1/q_n+sum_(j=1)^n w_n(j)T(1,j),
T(0,1)=1/q_m+sum_(i=1)^m w_m(i)T(i,1).
The waiting time and first nonempty jump decomposition follows by independent repeated rounds, not a continuous-time approximation. q_n<q_m for n>m: (1-1/x)^x increases for x>1, since derivative of its logarithm is log(1-1/x)+1/(x-1)>0 by log(1+t)<t; handle m=1 directly. Thus the first-exit waiting term has the desired positive sign. This is insufficient: the conditional jump can create several new blue vertices, improving continuation time. The precise unpaid lemma is
sum_i w_m(i)T(i,1)-sum_j w_n(j)T(1,j) < 1/q_n-1/q_m
for every n>max(m,3), with T defined above. Neither monotonicity nor the positive waiting term proves this signed weighted inequality. It is equivalent to the desired strict comparison, but exposes exactly where an improved coupling or potential bound must act.

Route3, star boundary and Bellman comparison: for m=1 the leaf seed forces the center deterministically in one round, so T(0,1)=1+t_1 where t_b=T(1,b). The center-seed value t_0 equals 1/q_n+sum_j w_n(j)t_j. Thus even the boundary requires
sum_j w_n(j)(t_1-t_j)<1/q_n-1.
For b<n, remaining leaves independently turn blue with probability (b+1)/n, giving the same one-dimensional triangular recurrence for t_b. This does not yield the needed uniform strict inequality automatically; all t_1-t_j are nonnegative by coupling, and could in principle offset the waiting advantage. No closed bound controlling that offset was established. A Bellman supersolution/subsolution approach would need explicit functions with residual signs and strictly separated singleton values; none was found. The noted K2,3 exception warns against claiming a dimension-free seed order, even though it lies outside n>3. No finite sweep, exact arithmetic program, numerical experiment, or CAS was run.

Disposition: HOLD, not refuted, solved, routine, or excluded for novelty. Current searches are bounded and do not establish registry clearance; the later Rice randomized-process source is a different model and its body was not acquired or relied upon. No actual applicable public proof of this conjecture was read. This is an identified incomplete mathematical bridge, not a generic worldwide-unknown veto. A future Lean route requires finite product transition kernels, absorption/expected-time semantics, exact source bridge, and the unpaid uniform comparison lemma first. No formal plan or dispatch for an unproved candidate.
