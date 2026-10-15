# Reading record, failed shortcuts, and review boundary

2026-10-14. Research candidate, not independently gated. All writes are
confined to this assigned directory; no staging, commits or subagents.

## Project reading

Read in full: AGENTS.md and upstream pin; R018; the complete 141-line I275
proof; I277 proof review and full reconstruction Sections 1–20; I283 endpoint
obstruction; the complete I346 moving-radius proposal, analysis,
reading-and-failures, and literature record. Large first combined tool
outputs were truncated; subsequent bounded targeted reads recovered the
complete I275/I277 arguments and I346 records. Completeness is not inferred
from hashes or prior PASS labels.

Read the complete retained cubic-torus paper entry, including actual scalar
Theorem intro:main and equality/complement statements. Its included upstream
proof sections were not audited. The catalogue's actual cubic-torus entry
and context were inspected; the complete preprint-tree JSON was parsed to
identify its 17 package paths and authenticate the entry blob. No complete
catalogue semantic read or full-manuscript duplicate audit is claimed.

Read complete retained AFM page-7/page-22 excerpts and freshly checked actual
Theorem 4.2 in the primary PDF. Crucially its conclusion is C^{1,beta}
convergence for beta<1/2, which gives the uniform Hölder bound used in the
new interpolation argument. Merely rereading "C1-small" summaries would
miss the rate-producing input. The full underlying classical regularity
proof is not audited.

I346 and the earlier authentication manifests were parsed as provenance
records; used local hashes are freshly recomputed in provenance.json.
Availability or authentication of any unconsulted manuscript is not
reported as semantic reading.

Primary web reads and exact theorem/equation extents are in literature.md.
Lacasse–Grest–Levine Section III was newly read beyond I346's abstract-only
scope. Its compression/contact relation already contains classical log–log
inversion. Lv's fixed-volume Appendix B.2 was also inspected. Milman's actual
scalar transition theorems were checked. No new full external source body
was written to disk. A primary TIB/WIAS PDF opening returned Internal Error;
its theorem content remains unread and is not used.

## Shortcuts rejected

1. I346's o(S) error cannot be divided by T2. The candidate instead derives
   S^(11/10)+S^2=o(epsilon^2/ell^2) from actual AFM Hölder control and energy.
2. C1 convergence has no assigned speed. The rate in (3.1) is proved by
   interpolation with a uniformly bounded gradient Hölder seminorm.
3. A fixed low-mode cutoff gives only o(epsilon) obstacle error and a fixed
   relative energy loss, insufficient here. All positive Jacobi modes are
   retained through their full inverse kernel; mean and translations are
   treated exactly.
4. A growing cutoff was not substituted into constants denoted C_N. No
   unproved moving spectral truncation estimate is used.
5. The actual polar inverse map is not replaced pointwise. Its image circle
   is used directly as the source curve. Its uniformly bilipschitz geometry
   controls the logarithmic kernel; A(p,0)=1 gives A-1=O(a^2) exactly.
6. No H1 point evaluation, guessed circular contact set, radial symmetry,
   Euler–Lagrange equation at contact, or quantitative contact-radius theorem
   is assumed. The lower bound may test any circle a=sqrt(epsilon/ell).
7. The four self traces must be counted: two sphere traces plus two separate
   face traces. Their combined compliance coefficient is 2/pi, producing
   the target energy coefficient 2pi.
8. Relative axial drift cannot simply be set to zero by moving E alone.
   The two actual inclusion inequalities are summed, canceling h identically.
9. The upper metric error is not bounded by a fixed O(d^2) fraction of S.
   The actual vertical area Hessian is I+O(r^2); its integrated weighted
   error is O(epsilon^2/ell^2). Fixed free-patch volume corrections have that
   same error after the constant-curvature linear variations cancel.
10. A constant-core cutoff with a=sqrt(epsilon) gives no log–log gain.
    The recovery is tangent to the parabolic obstacle at
    a^2[log(d/a)+1/2]=R epsilon, giving a^2~2R epsilon/ell.
11. A formal radial calculation proves only an upper bound. The candidate
    supplies a separate arbitrary-geometry lower bound on exact minimizing
    replacements, then recovers the full original class by minimization.
12. The cylinder branch is not given an o(delta) error and then normalized
    by T2. Its credited local value is exactly g(R), checked from the uniform
    spectral gap and explicit strictly nested tube/slab competitor.
13. Old leading contact/crossover results and the new algebraic crossover
    corollary are not separately nominated as substantial findings.

## Supporting checks and remaining review risks

checks.py uses exact rational identities for sphere-kernel coefficient
differences, four-trace factors, tangent-profile energy and crossover Taylor
coefficients. Its output is supporting algebra only, not proof of geometric
regularity or asymptotic uniformity. No simulation, finite optimizer or
Monte Carlo is used as proof.

The proof as written has no deliberately unpaid second-order estimate.
It is nevertheless a new discovery draft requiring independent checking,
particularly the uniform C^{1,1/4} bound under moving references, the trace
kernel identity on weighted actual C1 curves and its normalizations, and
exact-volume vertical area bookkeeping. If the AFM interpolation or inverse
kernel passage is rejected, the exact missing lower statement is

    for ball-localized exact replacements,
    D_R >= 2pi epsilon^2/(ell+log ell)-C epsilon^2/ell^2

uniformly in the joint limit. One must not fall back to the leading law and
claim that second order remains proved. The proof and contribution gates
are independent, and full formalization/external peer review are not claimed.
