# r172: the finite-witness reduction and its exact cost

PREFREEZE support calculation; no quantitative theorem is nominated.

Let A=C(X)⋊h Z and fix matrix sizes for positive elements a and b. Fix ε>0 and a norm-compact set K of pairs (a,b) in these corners such that a≼b for every pair. By the definition of Cuntz comparison, at each k=(a,b) choose a rectangular witness T_k with ||T_k* b T_k-a||<ε/3. Approximation in the crossed-product norm gives a finite Fourier polynomial witness with error still below ε/2. For this fixed T_k,

    ||T_k* b' T_k-a'||
      ≤ ||T_k* b T_k-a|| + ||T_k||² ||b'-b|| + ||a'-a||.

Thus the error is <ε on a neighborhood U_k in K. A finite subcover supplies T_1,...,T_m, a finite maximum Fourier propagation M, and a finite maximum witness norm. This proves qualitative uniformity on this SPECIFIED compact family. It produces neither an effective bound on m,M nor one depending only on mean dimension, trace gap, and ε. The topology and the compact family are essential data; the whole positive unit ball is generally not norm compact.

If K is a compact parameter space of such pairs, choose a partition of unity φ_i subordinate to these neighborhoods and put

    S(k)=(sqrt(φ_1(k))T_1,...,sqrt(φ_m(k))T_m)^transpose.

Then S is a continuous rectangular finite-Fourier witness and

    ||S(k)* b(k)^(⊕m) S(k)-a(k)||
       = ||Σ_i φ_i(k)[T_i* b(k)T_i-a(k)]|| < ε.

The last inequality uses the triangle inequality and Σφ_i=1. This construction is complete. Its target is b^(⊕m), not b. In a rank-allocation use, it can multiply the output rank by m; no strict K<2pn margin is thereby preserved. Patching the T_i in the original target would introduce cross terms, while averaging the positive errors alone is precisely what the column construction accomplishes. No impossibility of better patching is asserted.

The source avoids a need for this parametric patching: a single comparison in one crossed product gives one Fourier witness T_0 before choosing the orbit window. Its strict rank estimate is

    K_J/(pn) ≤ L + [R ceil(2M/k)+2p]/[pJ(H0-1)g],   L<2.

For the already chosen data it suffices, explicitly, to take

    J > [R ceil(2M/k)+2p]/[(2-L)p(H0-1)g].

This is an exact conditional arithmetic schedule after the witness has been obtained. It is not a bound on M from a radius equality. The companion then has a separate eventual-power threshold. Its finite-prime reduction needs inequalities of the form

    ceil(λ ell) ≥ f_MU(q)((e-d)ell+1)

at finitely many primes, and the large-prime connectivity inequality elsewhere. Sublinearity ensures some sufficiently large ell; the actual inputs do not provide a numerical universal inverse for these functions, or quantitative norms and propagation for arbitrary comparison witnesses.

Consequently no uniform comparison modulus is inferred. Compactness and stabilization already pay the finite-family construction above, but their rank cost must be accounted for in the same palette. This is the same compatibility issue exhibited by regular coinduction in DESCENT.md, without claiming that the two problems are equivalent.
