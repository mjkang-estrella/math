# Full shifted Jacobi law: ordinary candidate frozen for preliminary review

Source: Area 2608.23006v2, Definition 2.1 and Remark 3.8. Literal formal
polynomials only, not the still-conditional analytic phase identification.
For every r>=1, delta_r=2r+v2((r-1)!). Candidate credit0; total32/60 unchanged.

The full proof is the union of sol-jacobi-shifted-denominator-r3/discovery.md
(source-to-Riccati bridge, parity, degree, attainment) and
sol-jacobi-riccati-valuation-r4/PROOF.md (all-coefficient bound).
The source's Theorem1.4 is a published ordinary dependency, not yet Lean.
The original-variable denominator law is already proved in the companion;
MathDB391922 is that stale original-variable record, NOT this target.

Root read both full arguments and checked each load-bearing step. The new
integral quotient-ring proof appears valid as an ordinary argument:

- R=Z[x,w]/(w^2-x^2-1) has the unique free Z[x] normal form A+wB; its
  embedding into rational Laurent polynomials is injective.
- The two involutions have different roles. rho fixes x and negates w,
  commuting with the derivation, so odd b-degree selects w-odd coefficients.
  tau negates both x,w and anticommutes with the derivation; odd spectral
  indices have normal form A(x^2)+wx B(x^2).
- q(i,j)=s2(i)+s2(j)-1 is nonnegative on nonconstant monomials.
  Binary subadditivity proves closure under 2fg. Distinct monomials in a
  square pair with factor2; diagonal monomials use q(2i,2j)=q(i,j) and
  2q>=q. These are separate from pairing the spectral indices in the
  recurrence. No claim that the weighted class is a subring is needed.
- j odd implies q(i,j)>=s2(d-1) at d=i+j. Membership in the ideal(w)
  gives (1+x^2) divisibility of the w-even normal component over Z, including
  parameter coefficients. Division by the monic polynomial is integral.
- The w-even primitive vanishes at x=0. The w-odd primitive is w f(x^2),
  with triangular equation f+2(1+X)f'=-B. Only odd units 2k+1 are divided
  out, preserving every fixed dyadic divisibility bound. The primitive is
  tau-odd, so the source bridge has no hidden integration constant.
- Degree-d scaling s_n=2^(n+1-d) h_n and D=2 partial leaves primitive factor
  2^(n-d). At n=2r-1 this yields exponent2r-2-v2((d-1)!). Factorial divisibility
  then gives the required uniform bound. The substitution a=u+v,b=u-v is
  integral in the direction used; the inverse's halves are never invoked.

Root wrote an independent SymPy pair-ring recurrence and simultaneous linear
solve for the primitive. It compares with the earlier independently constructed
literal source coefficients through n=9, checks the parity/divisibility and
Laurent rescaling, and passes. check.py/checks.json are retained. These finite
diagnostics do not replace the ordinary all-order proof or independent review.

Review priorities: rederive the entire source bridge and both quadratic
pairings; challenge formal integrality, uniqueness, zero-degree/r=1 cases,
valuation attainment and exact question scope. Independently assess substantive
eligibility and current public prior art, including the same author's companion.
The proof uses classical tools but a concrete new filtered arithmetic assembly;
that is a hypothesis to test, not a supplied eligibility verdict. No global
priority claim. A purely routine published same-object bridge excludes credit.

The five Lean arithmetic helpers are tiny support only. No full FORMAL PASS:
literal source coefficients, logarithm/ODE bridge, quadratic ring filtration,
odd-unit primitive, factorial/binomial valuations, and assembly all remain.
The earlier parity/equivalence mistakes and failed checker are superseded only
where r3/r4 now supply genuine arguments; do not inherit their old assertions.

Frozen paths/hashes are in review-freeze.json, relative to the repository root.
No reviewer may edit the candidate, root notes, ledger, or shared files.
