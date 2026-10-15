# Parent source and proof check

Date: 2026-10-14. Candidate SHA-256 30bb73d2601754dcc6aa9eb26537e083256849acd3b5cf94a710970dfe067e54. This is parent evaluation, not an additional independent contribution gate or an acceptance.

## Reading

The parent read the complete candidate, its literature and failure records, and exact supporting program. This turn also read the complete I275 proof, complete I277 reconstruction Sections 1–20, complete I346 proposal and analysis, retained scalar source paper.tex including actual intro:main, and the complete retained AFM page-7/page-22 excerpts. A combined I346 read was truncated; targeted reads recovered the spectral split/circle argument in Section 7. The included scalar upstream proof sections and AFM underlying classical proof were not audited. The scalar source is stipulated true at the recorded pin. All nineteen recorded local input hashes and seven output hashes were checked previously; the exact algebra program was reproduced in a temporary copy with byte-identical output.

## Checked deductions

The scalar classification gives only ball and coordinate-tube inner endpoint limits and occupied coordinate slabs outside. Along a tube axis the tube has uniform cross-sectional area, whereas the ball leaves a third of the coordinate circle uncovered. The resulting L1 separation makes the two closed localization constraints disjoint. Low-energy localized minimizers approach their own orbit, so their constraint becomes inactive. Common ambient volume correction after lattice intersection/union preserves inclusion and establishes scalar quasiminimality for every comparison ball. This permits AFM's actual C1,beta graph conclusion for each set, including the disconnected outer boundary.

The cylinder spectral gap is uniform near rho=2/9 after removing the two transverse translations. Its constant mode is quadratic by exact volume. This yields an exact cylinder local minimum g(R), rather than an error subsequently divided by the smaller scale. The ball sphere gap and face Poincare inequalities give H1 norm O(epsilon/sqrt(ell)). Uniform C1,1/4 bounds and the elementary gradient-ball interpolation give C1 norm O(S^(1/10)); hence the area remainder S^(11/10)+S^2 is o(epsilon^2/ell^2).

For the sphere kernel, physical-area normalization cancels the radius factors from normalized spherical harmonics and Jacobi eigenvalues. Subtracting the mean-zero Laplace inverse leaves an absolutely uniformly summable coefficient difference; the removed first-degree term is bounded. Each actual deformed circle is bilipschitz at scale a, and the exact coefficient A(p,0)=1 makes A-1=O(a^2). Four self traces give compliance (2/pi)log(1/a)+O(1), with only bounded opposite-pole cross terms. The two face contributions are separate quadratic summands. The summed obstacle cancels relative drift. At a=sqrt(epsilon/ell) this gives the claimed lower coefficient and an O(epsilon^2/ell^2) loss. The source-curve trace approximation remains a key explicit independent-review target; no H1 point trace is used.

For recovery, the tangent logarithmic profile satisfies the parabolic obstacle and hence the exact spherical obstacle. Its four half-height patches have total energy J/2. Exact volume restoration cancels the inner first variation: sphere mean curvature 2/R is constant, so first area variation equals 2/R times the signed volume variation. Integrated r^2-gradient and bump errors are O(epsilon^2/ell^2); a fixed relative chart error would not suffice. The implicit contact-radius equation produces H=(ell+log ell)/2+O(1). The crossover is then elementary algebra with delta^2=o(T2), not a separate proposed finding.

## Remaining gates

No necessary repair was found in this parent check. Fresh independent full-scope proof review and separate contribution review are still pending. Classical contact/log-log inversion is credited; the proposed advance must stand on the unrestricted quantitative nonlinear bound. Nothing is accepted or counted here, and no full Lean or external peer-review certificate is asserted.
