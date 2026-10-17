# Family289: continuous unitary path lifting — technical screen

Disposition: **TECHNICAL, not nominated, not accepted**. This is an original derivation from stipulated source results and elementary operator-norm arguments, not an independent proof/contribution gate. No count change (10/20). Author Myeongjin Kang, no affiliation. Original prose CC BY4.0; third-party bodies remain private.

## Full question retained

Let H be any complex Hilbert space and let t ↦ M_t, t in [0,1], be a Kadison–Kastler continuous path of unital von Neumann subalgebras of B(H). Assuming the pinned universal strong stability theorem, there exists a norm-continuous U:[0,1]→U(H) with U(0)=I and U(t)M_0U(t)*=M_t. No factor, separability, expectation, differentiability or finite-dimensional restriction is imposed.

Here is a direct reduction paying the previously identified interpolation gap. Its ingredients are pointwise stability, the source's logarithm operation, and the standard successive-approximation selection method. Their combination does not provide a substantial new mechanism for this campaign.

## 1. Uniform short paths inside normalizers

For any norm-closed unital *-subalgebra P of B(H), suppose zPz*=P and ||z-I||<1/100. Put h=-i log(z), using the principal logarithm. Then h=h*, ||h||≤2||z-I|| and Ad_z=exp(i ad_h) as bounded operators on B(H). Since ||i ad_h||≤4||z-I||<0.04, the norm-convergent exponential and logarithm series are inverse here. Thus log(Ad_z)=i ad_h.

Every power of Ad_z-I preserves P, so its norm-convergent logarithm preserves P. Both exp(i s ad_h) and exp(-i s ad_h) therefore preserve P for all real s. Consequently z_s=exp(i s h) normalizes P. For 0≤s≤1,

    ||z_s-I|| ≤ ||h|| ≤ 2||z-I||.

This is precisely the first logarithm operation in source lemma `lem:small-exact-normalizer`, before its use of Sakai's theorem. That operation needs none of the separably acting typeIII hypotheses used for the subsequent controlled factorization. No continuous choice of that factorization is asserted or needed.

If a,b implement the same conjugacy from M_0 to P and ||a-b||<1/100, then a*b normalizes M_0. The path a exp(s log(a*b)) stays in the same implementing fiber and stays within 2||a-b|| of a. The same expression joins arbitrary sufficiently close unitaries in U(H), without the fiber assertion.

## 2. Closed fibers and Hausdorff continuity

Write F(t)={u in U(H): uM_0u*=M_t}. The unitary orbit class of M_0 along the path is open, and its complement is open: universal strong stability gives a positive KK radius in which any two algebras are unitarily conjugate. Connectedness of [0,1] therefore makes every F(t) nonempty.

Each F(t) is norm closed in the complete metric space U(H). Indeed, if u_j→u and u_jM_0u_j*=M_t, both inclusions pass to norm limits, applying the same argument to u_j*.

For any epsilon>0, source stability gives delta>0 such that d_KK(M_s,M_t)<delta supplies w with wM_sw*=M_t and ||w-I||<epsilon. Left multiplication u↦wu carries all of F(s) to F(t) and displaces each element by less than epsilon. The inverse gives the other Hausdorff inclusion. Thus F is uniformly Hausdorff continuous on the interval. This is stronger than lower semicontinuity; no global connectedness of a normalizer is assumed.

## 3. Approximate-selection improvement

Fix 0<epsilon≤1 and put d=epsilon/1000. Suppose f is a norm-continuous unitary path, f(0)=I, with dist(f(t),F(t))<d for all t. Given any eta>0, we construct a continuous unitary path g with g(0)=I,

    sup_t ||g(t)-f(t)|| < epsilon,
    sup_t dist(g(t),F(t)) < eta.

Set a positive h<min(d,eta/10). Choose a finite partition so that, on every interval [t_i,t_{i+1}], f varies from f(t_i) by less than d, and the Hausdorff distance from F(t) to F(t_i) is less than h. Choose v_i in F(t_i) with ||v_i-f(t_i)||<d, taking v_0=I. Choose b_i in F(t_i) with ||b_i-v_{i+1}||<h, using the Hausdorff inclusion at t_{i+1}.

Then ||b_i-v_i||<3d+h<4d<1/100. On the first half of the interval join v_i to b_i by the same-fiber short path of section1; on the second half join b_i to v_{i+1} by the ordinary short unitary path. These concatenate continuously, including the common v_i at partition points.

On the first half the new path belongs to F(t_i); its distance to F(t) is less than h. On the second half it stays within 2h of b_i, so its distance to F(t) is less than 3h<eta. Throughout, its distance from v_i is less than 8d+2h<10d. Adding ||v_i-f(t_i)||<d and ||f(t_i)-f(t)||<d gives ||g(t)-f(t)||<12d<epsilon.

The crucial improvement over direct interpolation between different fibers is that the long portion stays in a single exact fiber. Its error is controlled by the arbitrarily fine time partition h, independently of the allowed displacement epsilon. Only the final length-O(h) connector leaves that fiber.

## 4. Initialization and convergence

For any desired initial error d_0>0, take a fine partition on which source stability supplies implementers between M_{t_i} and every M_t in the interval with norm displacement less than rho, where 0<rho<min(1/100,d_0/4). Set v_0=I and recursively choose v_{i+1}=w_i v_i in F(t_{i+1}) with ||w_i-I||<rho. Ordinary logarithmic interpolation between v_i and v_{i+1} stays within 2rho of v_i. Every F(t) in that interval contains an element within rho of v_i, so the resulting continuous f_0 has dist(f_0(t),F(t))<3rho<d_0 and f_0(0)=I.

Choose epsilon_n=2^(-n-2), d_n=epsilon_n/1000, starting at n=0. Initialize f_0 with error below d_0. Apply section3 with epsilon=epsilon_n and eta=d_{n+1} to produce f_{n+1}. The increments are uniformly summable. Completeness of U(H) gives a uniform limit U, hence norm continuity and U(0)=I. Since dist(f_n(t),F(t))<d_n→0 and F(t) is closed, U(t) belongs to F(t). This proves the full conditional path statement above.

## Contribution comparison and reading limits

The source already supplies the entire quantitative conjugacy input and the small-normalizer logarithm mechanism. The remaining construction is the classical complete-metric successive-approximation selection operation. Michael's 1959 primary paper, *Convex Structures and Continuous Selections*, introduction and section8, explicitly places covering-homotopy selection in this framework and points to his 1957 finite-dimensional theorem. The 1959 theorem has additional convex-structure hypotheses: it is **not** being invoked without verification here. The direct one-dimensional proof above avoids that issue and also avoids assuming that a disconnected full normalizer is path connected.

Primary URL: https://doi.org/10.4153/CJM-1959-051-9 . Download receipt in primary-receipts.json. Only the introduction and section8 statement/proof were read; the full 1959 paper was not read. The CiteSeer copy of Michael1957 returned403, so its body is not claimed read. No literature-priority certificate, independent review, formalization or publication is claimed.

Decision: close this proposed acceptance route as TECHNICAL at its original full scope. Retain the paid interpolation argument for later supporting use, without counting it toward twenty.
