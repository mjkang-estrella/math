# I195 — the long-gap deficit

Status: COMPLETE written assignment, PARTIAL mathematical resolution. **Original-target verdict: UNRESOLVED at J195.** Unsealed proof-only record, created early with explicit partial status and updated incrementally. No decisive structural dichotomy or verified violating instance was obtained. Under the brief's stopping rule, leave the long-gap front for parent-side parking beside the already parked short-gap J194/J193 front and E183. No substantial finding is nominated.

The full proofs are in [analytic-attempt.md](../experiments/i195_long_gap_deficit/analytic-attempt.md). [reading-and-failures.md](../experiments/i195_long_gap_deficit/reading-and-failures.md) preserves failed routes and reading limits; [input-authentication.json](../experiments/i195_long_gap_deficit/input-authentication.json) records detached input hashes; [literature.md](../sources/i195_long_gap_deficit/literature.md) states source and contribution limits.

## 1. Authentication, domain, and exact residual

All seven brief anchors matched by detached SHA-256 before proof work: I194 `21f8e32eec69b89d7e6eade2763a3f7b125c6575121f5f05bddb0d37ab21b2b2`; I193 `e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5`; I192 `ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d`; I168 `696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31`; I169 `1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf`; I170 `8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096`; manuscript `03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56`.

The brief, all six finalized parent dispositions, I191's parking disposition, all three required analytic attempts, AGENTS.md, upstream metadata and catalogue are also hashed. The six reports and three analytic attempts were read in full before deductions. Actual manuscript ranges read: 60–140, 446–589, 794–837. All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true, without an upstream audit.

The domain remains B-admissible steps: G,H finite simple cubic bipartite planar 3-vertex-connected, with the facial deletion/insertion and complete six families of I192. All spaces are rational. The brace restriction additionally requires both graphs to extend every two disjoint edges to a perfect matching; it is not assumed automatically. With

    L=diff(N10∪N01∪N11), L0=Σ_(ij=10,01,11)diff(Nij),
    V=diff(N00), U=diff(Pux)+diff(Pvy)+diff(D11),
    ell=d(G)−dim L, t=dim(L0+U)−dim L0,
    beta=P+Q+D+2e+2f−A10−A01−A11,
    c=N−A10−A01+A11,
    eta=dim(L0+U+<beta>)−dim(L0+U),

I192 gives the exact deficit

    d(H)−d(G)−2=eta−Delta,
    Delta=ell−t=delta_V+epsilon−delta_R.

On long gaps k_A,k_B≥1, its facial classification gives V_good=0,R=U,delta_R=t,delta_V=dim(L0+V)−dim L0,ell=delta_V+epsilon. Here epsilon is the rank of c modulo L0+V. The full definitions of E_J and all residual spaces appear in the analytic attempt, Section 1. No translated old objects exist, but this does NOT imply U∩V=0. The exact bridge remains b=3r+2s_arc+a_P+a_Q+a_D; the completed a-objects are not old Hamiltonian cycles on long gaps and cannot be discarded. If N00 is empty, ell=0 and exchange already holds.

## 2. Exact cap-prism family theorem

For every even m≥8 and even j with 4≤j≤m−4, delete t_0,t_j on the top m-gon of C_m□K2, with terminal order T_0,T_1,T_j,T_(j+1). The complementary arc lengths are a=m−j−1 and b_len=j−1, both odd and at least three. These are exactly the requested long-gap cap deletions up to relabeling; the first is m=8,j=4.

The analytic attempt proves B-admissibility by a full vertex-deletion argument. The parent prism is also proved a brace by explicit matching extensions; child bracehood is not asserted or required for this B-family result. The complete old cycles are C_i (all rails except t_i,b_i, with rungs i,i+1), and X,Y (all rungs with opposite alternating rail matchings, X using even top rails). They are affinely independent. The old classes are exactly

    N00={Y}, N10={C_j}, N01={C_0},
    N11={C_i:i≠0,j}∪{X}.

The complete new classes are P_g (g∈{j+1,...,m−1}), Q_h (h∈{1,...,j−1}), and D_hg for all such pairs. Their explicit edge-vector formulas, degree-equation exhaustion and component/pairing proof are in Section 2 of the analytic attempt. Thus the six child-family sizes are 1,1,m−1,a,b_len,a*b_len.

Their differences satisfy

    U=span{C_g−C_g'}+span{C_h−C_h'} ⊆ L0,
    dim U=m−4, dim L0=m−2, dim L=m, d(G)=m+1.

Consequently, exactly

    ell=1, t=0, delta_V=0, epsilon=1, delta_R=0, Delta=1.

The lower-bound margin 1−Delta=t−(ell−1) is ZERO throughout this family. This is an equality family, not a strict-slack test. Nevertheless beta is independent. Writing Z for the sum of all rails, the complete-family formulas give

    P_g+Q_h=D_hg+Y,
    D_hg+e+f=C_h+C_g−Z,
    (m−2)Z=Σ_i C_i−X−Y.

The unique normalized functional on D_G/L, zero on surviving displacements and 1 on Y−C0, therefore takes the value

    w(beta)=m/(m−2)>0.

Thus beta∉L0+U, eta=1 and d(H)=m+3=d(G)+2 for EVERY stated cap deletion. These are written proofs, not finite enumeration.

In particular m=8,j=4 has exactly ten old cycles, child-family sizes (1,1,7,3,3,9), 24 child cycles, d(G)=9, dim L=8, dim L0=6, dim U=4, (ell,t,epsilon,Delta,eta)=(1,0,1,1,1), w(beta)=4/3 and d(H)=11. The full named edge families permit an independent parent check without any hidden data input.

## 3. General routes and their remaining gaps

The analytic attempt distinguishes two conditional multi-component constructions: Q+q_B, when Boolean, has k_B+1 components; Q−q_A+e+f, when Boolean, has k_A+2 components. Each count is proved by the noncrossing lemma with an auxiliary facial chord. Their required edge-presence patterns cannot be assumed. In the cap-prism family every Q_h satisfies the second pattern, while Q_h+q_B is never Boolean on a genuine long gap. Removing only the positive arc edges without adding the negative ones would not preserve degrees.

The exact flip criterion extends to a factor T with h components: if an alternating cycle's removed edges meet c components and the remaining paths pair endpoints by tau while added edges pair them by mu, the flipped factor has h−c+components(tau∪mu) components. This follows by suppressing the paths and retaining untouched cycles. It gives a test for reconnection, not a guaranteed reconnection. I194's fractional block identity extends to any number of components, but its outputs are old Hamiltonian differences; their cosets modulo L+U remain uncontrolled.

Splitting an even factor F into M1,M2 and taking its complement M0 gives F+(M0+M1)+(M0+M2)=2E. More component phases do not guarantee that either union is Hamiltonian. Brace two-edge extension does not provide that connectivity or the required span relations. The bridge extension's a-terms have fixed, potentially nonzero cosets modulo U; no identity like the prism's P+Q=D+Y is proved for arbitrary exteriors.

Finally, with W=L+U, kappa=dim(D_G/(D_G∩W)) and gamma=dim(W/(D_G∩W)), Delta=kappa−gamma. On a long gap even Delta=1 does not imply W⊆D_G. If the parent is separately affine-full it does, but V⊆W and a constant lost-family indicator still do not follow. Thus the short-gap normalized functional of J194 cannot be transplanted without additional hypotheses. No general comparison kappa≤gamma+1 or equality bridge exclusion was obtained.

The actual manuscript operations supply local existence and positivity of chosen spoke weights, with no proved transport of an arbitrary L0+U-annihilator. I178's fixed thirteen-vertex, five-port interface is not identified with an arbitrary four-terminal step, so its relations are not used to supply missing ranks. D168 and M168 remain binding method obstructions.

## 4. Remaining assertion, stopping rule, and limits

> **J195 (unpaid).** For every B-admissible long-gap step with N00≠∅ and the actual complete families above,
>
> t≥dim(L0+V)−dim L0+epsilon−1;
>
> if equality holds, beta∉L0+U.

This is precisely J192 on long gaps, with the brace restriction also unresolved. It is equivalent to long-gap exchange because eta∈{0,1}. Its failure locus is Delta≥2, or Delta=1 with beta∈L0+U. No fully specified violating step is exhibited. The cap-prism theorem proves both clauses on that infinite family; the general elementary branches ell=0 and t≥ell are settled by eta≥0, and a singleton N00 always settles the first clause only.

**UNRESOLVED without a decisive new constraint.** The cap-prism result has singleton N00 and does not give a high-loss dichotomy. The multi-component statements and failed-route analysis do not force J195. Apply the brief's stopping rule at parent level; no further long-gap or short-gap iteration is proposed. E183 and its dependencies remain parked.

A proof of both long-gap clauses would reduce universal exchange exactly to the PARKED short-gap bridge J194/J193, since the short-gap rank bound is already paid. It would not settle that bridge. Q164/(T) and affine fullness gain conclusions only through the FULL exchange theorem and the applicable paid reductions, not from this family calculation or from long-gap exchange alone. No all-brace construction claim is made.

Only the five assigned paths were written. No research code, scans, tests, experiments, replay/rebuild, source copies, snapshots, seals, further agents, ancestor/shared-ledger edits, staging, commits or publication occurred. Authentication binds input bytes; historical finite results were not freshly verified. No external theorem was invoked unread, no new-to-literature claim is made, and no substantial finding is nominated. Final output digests are returned detached, without a self-hash or seal.
