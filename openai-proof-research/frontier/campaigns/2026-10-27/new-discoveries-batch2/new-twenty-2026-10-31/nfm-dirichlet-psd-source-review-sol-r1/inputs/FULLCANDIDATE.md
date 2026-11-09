# 352259: author ordinary proof proposal, unqualified and uncredited

This is a full ordinary argument for the actual NFM source Conjecture 3.5, not an independent PASS. Exact MathDB literal is preserved in originals/352259.jsonl and provenance.json. The literal calls the sufficient condition “Theorem 2”; the downloaded actual 2110.08385v1 calls it Theorem 3.4 and points to that theorem in Conjecture 3.5. This label discrepancy must be explicitly adjudicated, not silently treated as a new result. The defining subgraphs, cutoff range, probability quantifier and sufficient inequality agree. No different graph model is substituted.

## Actual definitions and full endpoint

Fix finite k>=2 and a fixed vector alpha of finite strictly positive Dirichlet parameters. Symmetry of alpha is unnecessary. Sample theta^1,...,theta^n independently from Dirichlet(alpha). The actual weights are W_uv=log(z_uv/(1-z_uv)) for u!=v, z_uv=<theta^u,theta^v>, with zero diagonal. They are NOT the affine weights 2z_uv-1. For a cutoff t let V'_j={u:theta^u_j>=t}. Let U_j consist exactly of nodes incident to a negative edge of the induced graph. We prove that there is one t in (1/2,1/sqrt(2)), depending only on k,alpha, such that simultaneously for all j, with probability tending to one, there is S_j subset V'_j minus U_j satisfying

|S_j| W_us >= -2 sum_{v in U_j:W_uv<0} W_uv

for every u in U_j and s in S_j. This is the actual entire source hypothesis, stronger in probability than requested. It does not assert recovery of all original fringe nodes or the different Conjectures 3.2,4.2,4.5.

## Constant choice (before n)

Set a=1/sqrt(2), b=9/10, t0=3/5. Then 1/2<t0<a<b<1 and b*t0=27/50>1/2. Write ell(z)=log(z/(1-z)) and c=ell(27/50)=log(27/23)>0. Put pi_j=P(theta_j>=b) and pi=min_j pi_j. Each pi_j is strictly positive. Indeed the Dirichlet density is strictly positive on the interior of the simplex, and the open cap theta_j>b contains a relatively open set with compact closure in that interior and positive (k-1)-dimensional volume. On this compact set the continuous positive density has positive minimum. Thus its integral is positive. There are finitely many j, so pi>0. This argument includes every finite positive alpha, even if its boundary density is unbounded.

The function eta(t)=-ell(t^2)=log((1-t^2)/t^2) is positive and continuous for t<a and tends to zero as t increases to a. Choose and fix t in (t0,a) such that eta(t)<pi*c/4. Existence follows from this one-sided limit; t depends on the distribution but never on n or the realized sample.

## Deterministic bounds, all nodes at once

Define S_j={s:theta^s_j>=b}. It is contained in V'_j. For distinct nodes in V'_j, nonnegative simplex coordinates imply z_uv>=theta^u_j theta^v_j>=t^2. Since ell is increasing, every negative weight satisfies -W_uv<=eta(t). For a node s in S_j and any other v in V'_j we have z_sv>=bt>=bt0=27/50, so W_sv>=c>0. Consequently S_j is disjoint from U_j; this conclusion uses positivity against ALL other nodes, not only against U_j or against strong nodes.

For every u in U_j, the negative incident mass is at most n*eta(t). No independence between edges is needed. On the event |S_j|>=n*pi/2,

|S_j|W_us >= n*pi*c/2 > 2n*eta(t) >= -2 sum_{v in U_j: W_uv<0}W_uv.

This proves the exact simultaneous hypothesis. When U_j is empty the condition is vacuous, as it should be; no nonempty-U assumption is introduced. The argument does not require the number of negative edges to be small.

## Probability and quantifiers

For fixed j, |S_j| is a sum of n independent Bernoulli(pi_j) variables. Its mean is n*pi_j and variance n*pi_j(1-pi_j); the latter follows by expanding the square and using independence to cancel cross covariances. Markov's inequality applied to the squared centered variable gives

P(|S_j|<n*pi_j/2)<=4(1-pi_j)/(n*pi_j).

Since pi<=pi_j, failure of |S_j|>=n*pi/2 is contained in this event. A union bound over the fixed finite k gives failure probability at most (4/n) sum_j (1-pi_j)/pi_j, which tends to zero. Thus one fixed t works for every j simultaneously. This proves the weaker “not converging to zero” assertion as well.

Dirichlet samples lie in the strict simplex interior almost surely for positive parameters. For k>=2, this makes 0<z_uv<1 for distinct nodes almost surely: positivity gives the lower bound, and z_uv<=max_i theta^u_i<1 gives the upper bound. All graph weights are therefore finite almost surely for each finite n. The event of finite weights for all n can also be imposed under the usual infinite iid coupling by countable union. No uniform upper bound on positive weights is used. k=1 is a definitional boundary: the displayed NFM logit is infinite on every edge when n>=2, so it does not generate a finite signed graph. The proposal covers every nondegenerate finite-weight NFM instance; root must adjudicate this standing-domain issue in binding an exact literal theorem. It is not offered as a k=1 correction/refutation.

## Independent energy derivation of the PSD consequence

The candidate's target is the combinatorial hypothesis, so the source PSD theorem may be attributed. There is also a direct ordinary verification of the consequence in our stronger uniform setting. For a real vector x, put A=mean_{s in S} x_s and d_-(u)=sum_{v:W_uv<0}|W_uv|. The weighted Laplacian energy is sum_{unordered uv}W_uv(x_u-x_v)^2. The total negative contribution has absolute value at most 2 sum_{u in U}d_-(u)(x_u-A)^2, by (x_u-x_v)^2<=2(x_u-A)^2+2(x_v-A)^2. The positive U-S contribution is at least c sum_u sum_s(x_u-x_s)^2 >= c|S| sum_u(x_u-A)^2. Our inequality c|S|>=2d_-(u) proves nonnegative energy; all discarded positive edges help. If U is empty, PSD is immediate. On our event S is nonempty for all sufficiently large n. No source proof sign convention is imported here.

## Failed shortcuts and scope controls

All edges cannot simply be declared positive below a. For k>=3, vectors near (t,1-t,0,...) and (t,0,1-t,...) have inner product near t^2<1/2; negative edges persist with positive probability. Bounding only the number of fringe nodes is unnecessary and would demand a stronger distribution estimate. A fixed set of pure vertices has probability zero under a nondegenerate Dirichlet law; we use an OPEN cap of positive measure instead. Allowing b or t to depend on n would not prove the requested assertion; both are fixed first. Pairwise edge independence is false, but only iid node indicators are used. For k=2 all within-selected-cluster weights are already positive for t>1/2; that special case is not a separate family.

## Source, prior and significance gates

Primary body sources/nfm.pdf SHA256 79c103fa85578bc9f54a88fffb2e938493a8e5f396d3cf1f0ec9d1be9afc32ce, 2110.08385v1. Definition2.1, Section3.2, Theorem3.4, Conjecture3.5 and the full Theorem3.4 proof were read in extracted text. Actual pages8/9 were visually inspected; page8 initial presentation parsing failed after output truncation, recovered with smaller render; original evidence retained. No whole-paper/figure/internal SDP audit is claimed. Official current abs body shows only v1, submitted15Oct2021, no journal reference displayed; this is bounded metadata, not a certificate of no final/correction. A same-topic dissertation Chapter5 appeared in search at a forbidden /server/api/.../content URL: NEVER requested, no API permission inferred, and its actual conjecture/proof passages remain unread. The search excerpt does not assert a matching resolution.

All883 permitted historical files were hash-authenticated after pre-access path filters; exact reserved-ID keys/scalars gave no matches. Source-neighbor matches for other targets were reconciled separately. This is not a full personal comparison of all96 accepted proof scopes or a certificate of family nonoverlap. Search3 targets public proof terms and GitHub; four inherited unavailable registry roots were not retried or indirectly reconstructed. Three calls/nine queries are charged and full responses saved. No authenticated matching public proof was found in this bounded navigation; no worldwide novelty is asserted.

Strongest significance objection: the actual source already supplies Theorem3.4 and even explicitly uses iid fringe counts and Hoeffding in Example3.1. The exact source-to-target application consists of the fully paid fixed-core mass, logit continuity, uniform negative-mass bound and binomial concentration above. Thus there is a COMPLETE elementary source-result-to-target bridge supporting a routine-application objection; shortness alone is not that objection. Strongest contrary case: Conjecture3.5 is deliberate, all positive parameter vectors and all clusters are settled simultaneously, the strict t<a interval genuinely includes negative edges, and the source does not print this argument or conclude its own conjecture. Neither earlier exact public solution nor independently adjudicated routine exclusion is claimed. Root significance review is required. This proof is author evidence only and has ZERO accepted credit.
