# T205Q140: frozen author target

Freeze UTC: 2026-10-20T21:50:46.560767+00:00

For every integer m>=2 let n=m(m+1)/2, rho=(m,m-1,...,1), and let chi_lambda and d_lambda be the ordinary complex irreducible character and dimension of S_n indexed by lambda. Let g denote ordinary Kronecker multiplicity. Define

K_m(lambda,nu)=g(lambda,rho,nu)d_nu/(d_lambda d_rho),
pi_n(lambda)=d_lambda²/n!,
mu_m(lambda)=K_m²((n),lambda)=g(rho,rho,lambda)d_lambda/d_rho².

No laziness or continuous-time conversion is applied. All partitions of n are states. Total variation is one half of the l1 difference; chi²(q,pi)=sum_lambda (q(lambda)-pi(lambda))²/pi(lambda). Let C3 be the class (3,1^(n-3)), of size n(n-1)(n-2)/3, and X_n(lambda)=sqrt(|C3|)chi_lambda(C3)/d_lambda. Put a_n=sqrt(|C3|)/[4(n-2)²].

Prove all of the following as ONE author theorem:

1. There is an absolute finite constant C>0 such that, for EVERY integer m>=2,
   E_pi[(mu_m/pi_n-1-a_n X_n)²] <= C/n².
   The residual is orthogonal to X_n and to constants. In particular
   0 <= chi²(mu_m,pi_n)-n(n-1)/[48(n-2)³] <= C/n².

2. For EVERY m>=2, the maximum over ALL initial states lambda of the two-step total variation distance is attained at the trivial state (n) and equals TV(mu_m,pi_n). The same assertion holds for chi². As m tends to infinity,
   sqrt(n) max_lambda TV(K_m²(lambda, .),pi_n) -> 1/[4 sqrt(6 pi)],
   n max_lambda chi²(K_m²(lambda, .),pi_n) -> 1/48.
   Here pi in the first limit is the circular constant.

3. For EVERY m>=2, max_lambda TV(K_m(lambda, .),pi_n)=1-pi_n(rho), and this tends to1 as m tends to infinity. Thus the result specifies an abrupt one-to-two-step transition; it does NOT use the conventional cutoff term requiring diverging mixing times.

Dependencies: classical finite-group character algebra and the exact tensor-chain diagonalization (Fulman), Murnaghan--Nakayama and staircase 2-core structure, Feray--Sniady theorem1 (v4), Teyssier theorem1.2 (2508.06770v2, September16,2026), and Fulman's i-cycle CLT theorem3.14. Pinned source205 support/proof operations are credited and stipulated true, but its positivity conclusion is NOT needed for this analytic proof. No symmetric/exterior, integral/modular, nontriangular, general self-conjugate, or pointwise relative-multiplicity conclusion is appended. Old R037, R026 and I19/I21 full targets remain unchanged.

Chronology: This freeze follows initial source and primary reads, exact all-support summation feasibility, a leading-term calculation, and bounded exact diagnostics m=2..6 (full decomposition only throughm=5). The outline of the entire proof already exists in working notes; this is disclosed prefreeze feasibility, not a claim of discovery after freeze. It precedes extended full author-proof drafting. Source/history reads were partly late relative to the first calculation and are enumerated in reading-limits. This exact file will not be edited.

This is a proposed full author-proof target. It assigns no independent correctness, substantiality, acceptance, campaign count, formal-support, manuscript, or release gate. Its residual contribution is the uniform fourth-moment summation over every odd-cycle profile, especially the intermediate support window; whether this is substantial rather than a technical composition is reserved to a separate independent review. No worldwide-priority claim.
