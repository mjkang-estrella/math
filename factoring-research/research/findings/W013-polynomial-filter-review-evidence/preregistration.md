# Fixed exact algebraic certificate preregistration

2026-10-08 UTC. This file is written before creating or executing the certificate.
Review object: frozen W013.md Card B, SHA-256
f20282daba4ebd972246328c4641d80ac5472c5173065c48e1b52acc43bfb2f9.
No parameter selection, numerical search, factor search, performance measurement,
prime/depth sweep, or solver experiment is authorized or planned.

One standard-library Python certificate will perform these predetermined exact
checks, using integer polynomials and fractions only:

1. Degree-four reciprocal Taylor identity after clearing denominators, retaining
   the negative sign of the remainder.
2. Five-node Newton interpolation identity for symbolic X,m,h after clearing
   D=product_{j=0}^4(X+j*m), and the symbolic quadratic numerator
   X^2+10*X*m+35*m^2.
3. Five Lagrange basis polynomials at the fixed nodes 0,1,2,3,4: exact nodal values,
   quadratic coefficients 35/24,-13/3,19/4,-7/3,11/24 and absolute sum 40/3.
4. Three fixed illustrations of essential scope restrictions, not counterexamples
   to the theorem: A(h)=0 modulo 5 has five roots; h^2 modulo 16 has four roots;
   h(h-1)/2 is integer-valued at the five fixed interpolation nodes but has
   nonintegral monomial coefficient 1/2.

The general-d Taylor argument, integer-node ranges, inequalities, floor/filter
logic, and asymptotic scope are proved by hand in the report. This certificate
checks identities and examples; it is not a Lean proof or a complexity theorem.
Success: every stated identity and expected coefficient matches exactly.
Any error, exception, failed assertion or missing check must remain in recorded
execution output. No replacement instances. Output and script receive SHA-256
hashes in the delivery manifest. No shared files are changed.
