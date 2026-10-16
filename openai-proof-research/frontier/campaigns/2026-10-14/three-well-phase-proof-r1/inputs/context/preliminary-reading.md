# P3R parent preliminary reading

2026-10-16. Myeongjin Kang, no affiliation. Original prose CC BY 4.0;
original checker MIT. This records a reading of saved, potentially still active
author work. It is not terminal task integration or an independent proof PASS.
Count remains 5/10. No author bytes were edited.

Read the entire frozen scope, candidate Sections 1–10 and checkpoint list.
The exact observed candidate and scope hashes are in algebra-receipt.json.
The orchestration service rejected repeated status requests with
`parent_not_active`; this does not establish that the analytic-r15 task stopped.
Do not restart or assign its family to another discovery agent on that basis.

The full proposed target is unchanged: every a>0, 0<rho<1/2, finite m>=3,
all realizations of the specified signed Grams, exactly three negative
eigenvalues at every separation, all corresponding one/two-well subsystem
spectra equal, full-trace sign reversal, and the precise positive limit
4096 a^4 rho^3/pi^3 after division by R^2 exp(-4aR).

## Direct mathematical checks

1. The scalar factorization has the correct partner sign. With b=2a nu,
   q=b tanh(2ax), q^2-q'=b^2-4a^2 nu(nu+1)sech^2(2ax), whereas
   q^2+q'=b^2+4a^2 nu(1-nu)sech^2(2ax). Thus the restriction lambda<2
   really is what gives nu<1 and the nonnegative partner correction.
   This does not assume the three separated wells are pointwise orthogonal.

2. The lifted bracket is a valid quadratic-form operation: before separate
   translations, conjugate G tensor R0 by the diagonal multiplication
   operator. Both bounding scalar channels are scaled by d=1-2rho and
   c=1+2rho, and both lie in (0,2). At each k>0 the upper bound has at
   most three eigenvalues above one; taking k below b_d yields at least
   three for the lower bound. The passage to all negative eigenvalues
   therefore excludes extra eigenvalues accumulating at zero. A reviewer
   should still inspect the precise Birman–Schwinger counting interface.

3. At coalescence f(lambda)=2+3lambda-2sqrt(1+3lambda), so
   f'''=-81/4 (1+3lambda)^(-5/2). Integrating the centered second
   difference of F' over [-rho,rho] gives exactly
   F(2rho)-F(-2rho)-2F(rho)+2F(-rho). Its strict negativity follows
   because F' is strictly concave on the entire required interval.

4. Closed walks on the three-vertex loopless graph have even incidence
   degree at every vertex. Hence all three edge traversal counts have
   identical parity, and that common parity equals the total length's
   parity. Flipping edge13 cancels every even trace term exactly, not just
   its asymptotic approximation. There are six oriented length-three
   walks, supplying the factor -4rho^3 after the logarithm's -1/3.

5. For B12 and B23, the rank-one direction is v_plus odot v_minus;
   for B31 it is v_minus odot v_plus. Their cyclic product trace is
   [v_minus,A v_plus][v_minus,A v_minus][v_plus,A v_plus]/(2k)^3.
   Thus the mixed/pure pairings in (7.4) have the right order. At k=a
   all three residues are 2a A_tail^2; dividing their product by (2a)^3
   gives the coefficient A_tail^6 of the third-order pole.

6. If h has Laurent coefficients h_-3,h_-2,h_-1, direct multiplication
   gives the residue of k exp(-4kR)h as exp(-4aR) times

       8a h_-3 R^2 - 4(h_-3+a h_-2)R + h_-2 + a h_-1.

   Combined with the trace formula's outer factor 8rho^3, this yields
   64a A_tail^6 rho^3, with the stated sign. The dimensions also agree:
   a^4 R^2 has the units of an energy. This is a residue calculation,
   not a replacement of the continuum operator by a three-state model.

Independent exact finite controls passed 40 Gram characteristic evaluations,
all loopless closed walks of lengths2–10, and243 residue coefficient cases.
Only Python integers/Fraction were used; no floating-point spectral evidence.
The initial SymPy availability probe failed, so no symbolic package was used.
The general arguments above are separate from these finite controls.

## Obligations for the eventual independent review

P1. Authenticate the completed author package once delivered. Saved source
bytes alone are not a sealed final handoff. Read actual family262 statements
and companions; this preliminary parent reading does not claim that source
audit or a primary-literature contribution comparison.

P2. Check closed-operator domains in the scalar intertwining argument, the
trace-class analytic factorization for complex k, determinant multiplicities,
and that a zero in Re k>0 really corresponds to the physical eigenspace.
The displayed derivative is negative on the kernel; justify its conversion
to zero multiplicity and the argument principle on the chosen disk.

P3. Check the logarithm on an annular neighborhood of the contour, rather
than implicitly extending a small-norm series through its central pole.
Only its single-valued contour branch is needed for integration by parts.
The full-spectrum bracket and three-zero argument must both be retained.

P4. Check the smooth-tail error uniformly for complex k on the full contour,
the trace ideal estimates, reverse transposition, and all remainder terms.
The claimed exponents are consistent: adjacent-block replacement costs
2a+3(0.9a)=4.7a, the long-block error costs4a+2(0.9a)=5.8a,
and the higher-log terms cost5(0.9a)=4.5a. Polynomial factors can be
absorbed into the4.5a bound for tail errors, leaving a strict gap over4a.

P5. Separate substantive contribution from established multiple-scattering
determinants, supersymmetric scalar spectra, Bargmann phases, and finite
graph loop signs. The full continuum observable, exact pair equivalence,
all-R negative-state count and reversal may form one result; none should
be counted separately. A new explicit constant alone is insufficient.

No blocking mathematical contradiction was found in this preliminary reading.
That is weaker than full proof/contribution acceptance. Wait for authenticated
terminal delivery before commissioning the required independent review;
preserve all scope and the above obligations in its brief.
