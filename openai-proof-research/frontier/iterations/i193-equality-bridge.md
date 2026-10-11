# I193 — short-gap equality bridge

Status: COMPLETE written assignment, PARTIAL mathematical resolution. **Original-target verdict: UNRESOLVED.** This is an unsealed proof-only record. The five files were written early with PARTIAL status and updated as the reading and proofs stabilized. No substantial finding is nominated. E183 and its named dependencies remain parked.

The same-square comparison and two-step composition now have exact written answers: complementary deletion pairings have the same equality coefficient; a hypothetical failed short-gap step gains one dimension and either following central-square expansion gains three. Neither deduction excludes the failing coefficient or realizes a failing graph.

Full proofs, including the equality reduction, composition identities, conditional exclusions, and inherited prism family, appear in [analytic-attempt.md](../experiments/i193_equality_bridge/analytic-attempt.md). Failed routes and reading limits are retained in [reading-and-failures.md](../experiments/i193_equality_bridge/reading-and-failures.md); exact input digests are in [input-authentication.json](../experiments/i193_equality_bridge/input-authentication.json); source and contribution boundaries are in [literature.md](../sources/i193_equality_bridge/literature.md).

## 1. Authentication and domain

Before proof work, detached SHA-256 authentication matched all five required anchors:

* I192: `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d`.
* I168: `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31`.
* I169: `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`.
* I170: `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096`.
* Retained manuscript: `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.

The brief, all four finalized parent dispositions, the I191 parking disposition, the I192 analytic attempt, applicable AGENTS.md, upstream metadata, and catalogue are also authenticated in the JSON. The required reports and analytic attempt were read in full before new deductions; actual manuscript lines 60–837 were read. All OpenAI results at the pinned revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true, without auditing their truth.

The domain is exactly I168–I170's B-admissible steps: G,H are finite simple cubic bipartite planar 3-vertex-connected graphs; disjoint facial edges e=uv,f=xy occur in terminal order u,v,...,y,x,...; their replacement consists of arms up,vq,xr,ys and square pq,qs,sr,rp on four new vertices. The target assumes at least one complementary arc is a single edge. Statements apply in particular to brace steps, but no all-brace construction is assumed. All spaces are over Q.

## 2. Equality case and its surviving gap

Use the complete Hamiltonian families Nij, S=N10∪N01∪N11, L=diff(S), V=diff(N00), and the three complete exterior families Pux,Pvy,D11. Set U to their summed difference spaces, ell=d(G)−dim L, t=dim(L+U)−dim L. The exact bridge b and rank eta give

    d(H)−d(G)−2=t+eta−ell, eta∈{0,1}.

For a=ux a one-edge arc, put Z=diff(Pvy), W'=L+V+Z, r=N−C0 and

    F_Q=Q−a+e+f, z=F_Q−C0.

The inherited bijections yield U=V+Z, b=r+2z mod W', and t≥ell−1. The object F_Q is an actual spanning two-factor with exactly two components, one closed by e and the other by f. In the equality case t=ell−1, dimension forces D_G=W'+<r> and r∉W'. If z∉D_G, exchange holds. Otherwise z=lambda r mod W' has a unique, anchor-independent coefficient and

    exchange fails iff lambda=−1/2.

Equivalently the unique normalized quotient functional w has w(r)=1 and lambda=w(F_Q−C0). Its affine values are 0 on S and 1 on N00. On a quadrilateral, s0=e+f−ux−vy, U=V, z=r+s0, and lambda=1+alpha where s0=alpha r mod (L+V). Thus the same failure is alpha=−3/2. These are paid reductions, not a new exclusion theorem.

## 3. Written deductions from the requested composition route

**Complementary deletion symmetry.** On one quadrilateral let A be the cycles using only ux,vy on the square, B those using only e,f, and T those using three square edges. These are all possible Hamiltonian patterns, since each terminal needs a square edge and the whole square cannot be an isolated cycle. Taking a base in T, minus the sum of the four square coordinates has affine value 1_A+1_B. Therefore an affine indicator h_A for A exists exactly when one for B exists, via h_B=−sigma−h_A. Such an indicator exists exactly when its deletion pairing has the equality deficit ell−t=1. The deficits of the two pairings consequently coincide. In the equality case with s0∈D_G,

    alpha_B=h_B(−s0)=h_A(s0)=alpha_A,

because sigma(s0)=0. If s0∉D_G both bridges are independent. In the zero-deficit case both W spaces equal D_G and the bridge ranks again coincide. Thus the two expanded graphs have the same Hamiltonian affine dimension and the same exchange outcome. Pairing the expansions supplies no opposite-sign bound.

**Central-square composition.** In the first child H, expand its central square by deleting pq,rs. Its lost family is precisely the original D11 fibre. For child new-class differences x_P,x_Q,x_D and the homogeneous transport map T0, the exact relations are

    D_H=T0(W)+<x_P,x_Q,x_D>, W=L+U,
    x_P+x_Q+x_D=T0(b).

Their only relation modulo T0(W) is governed by b∈W. An affine indicator of the lost D11 fibre must take values 0,0,1 on the three displayed differences and vanish on T0(W). It exists exactly when b∉W. Hence for the central successor

    Delta_c=ell_c−t_c=eta_first.

On a short gap, with aligned representatives and s_c=pq+rs−pr−qs, direct coordinate comparison gives

    s_c=T0(z)−x_D, s_c∈D_H iff z∈W+<b>.

If the first equality coefficient exists and lambda≠−1/2, this also proves the exact transport formula

    lambda_c=lambda/(1+2lambda).

If the first step instead fails (lambda=−1/2), then its eta=0, its z is outside W, and the central successor has Delta_c=0, eta_c=1. Therefore

    d(H)=d(G)+1, d(J)=d(H)+3=d(G)+4.

Complementary central deletion has the same result by the first symmetry. This is a conditional rank-recovery theorem, with admissibility proved in the analytic attempt; it is not a construction of a failed step. The two-step gain is compatible with a first-step failure, so it gives no contradiction.

## 4. Structural routes and settled subcases

The actual manuscript cancellation and positive-circulation argument chooses special weights to prove existence of a forest state. It supplies no identification of those weights with w, no weight-preserving reconnection of F_Q, and no quotient positivity inequality. The Pfaffian orientation definition does apply to both even components of F_Q, but its orientation parity does not determine this rational functional. Brace matching extension yields matchings, without guaranteeing that the resulting two-factors are connected.

An exact convex representation of F_Q by Hamiltonian cycles is impossible: zero coordinates outside F_Q would force every positively weighted cycle to be contained in, and hence equal to, F_Q. A convex representation only modulo W' is a different, unpaid assertion.

The following successful subcases are proved in writing:

* ell=0 or t≥ell, directly by eta≥0; in particular the formal N00-empty case.
* Equality with z∉D_G, or with an existing coefficient lambda≠−1/2; on quadrilaterals the equivalent s0/alpha conditions.
* If every individual alternating-cycle flip from a surviving Hamiltonian C toward F_Q remains Hamiltonian, then w(F_Q−C0) is a sum of 0/1 values and is nonnegative.
* If z is in the integer span of old Hamiltonian differences, then lambda is an integer.
* More generally let phi be the primitive integer functional on Gamma=D_G∩Z^E with kernel Gamma∩W', oriented so m=phi(r)>0. If m is odd, lambda=phi(z)/m cannot be −1/2. No general oddness of m is established.
* Any central-square successor of a step with eta=0 has zero deficit and satisfies exchange; after a failed short-gap step its gain is exactly three.
* Every lateral-square expansion of every even prism C_m□K2, m≥4, has lambda=1/(m−2)>0 and d(H)=d(G)+2. The complete exhaustion, affine independence, coordinate identity and admissibility proof are included, at the inherited P169 scope.

Every quadrilateral and hexagon has a short gap by odd complementary-arc lengths, but that fact does not settle their remaining equality coefficient. No failed coefficient is inferred from formal rank patterns. The historical finite evidence contains no failing step, and no new graph is offered.

## 5. One precise remaining assertion and limits

> **J193, unpaid:** For every B-admissible short-gap step with its actual complete families, if t=ell−1 and F_Q−C0∈D_G, the unique normalized quotient functional w on D_G/W', with w(N−C0)=1, satisfies w(F_Q−C0)≠−1/2.

This single assertion is exactly equivalent to the requested short-gap exchange theorem after the settled branches above. Its restriction to brace steps remains unresolved too. **SHORT-GAP EXCHANGE PROVED** and **REFUTED** are both unsupported; the original-target verdict is **UNRESOLVED** at J193.

The secondary both-long-gap clause was not pursued because the primary did not resolve. The long-gap parts of J192 remain open. Even a proof of J193 would leave universal exchange and Q164 unproved. The count bound historically called Q164 and the stronger affine-fullness target receive no new conclusion.

The new written symmetry and composition deductions are only claims at their proved mathematical scopes, without literature-priority certification or substantial-finding nomination. Exactly the five assigned files were written. There was no research code, graph/state/matching scan, test, experiment, sealed replay/rebuild, source copy, snapshot, seal, further agent, ancestor/shared-ledger edit, staging, commit, archive, publication, or parent integration bookkeeping. Final hashes are returned detached; this remains an unsealed proof record.
