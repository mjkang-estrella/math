# Checks for the T298P round-2 proof review

All scripts are reviewer-written for this review. They do not import or reuse author or round-1 code. They support review.md; they do not prove any entropy statement.

| Script | Output | Interpreter | What it checks |
|---|---|---|---|
| exact_adjoint.py | exact_adjoint.json | `python3 -I -B` (stdlib, exact Fractions) | Inner-leg adjoint identity, Leibniz rule, centrality of w_bc and the matrix contraction (1/k)(E_cb ⊗ Ξ) for free semicircular test variables, k = 2, 3. Two negative controls (transposed matrix unit; dropped correction term) must be detected. |
| finite_geometry.py | finite_geometry.json | `/var/tmp/r99-eval-env/bin/python -I -B` (needs numpy) | Coarse inverse and leading coefficient; noise covariance; almost-commutation constant; arbitrary-size recovery pipeline (bands, truncated polar tree maps, root intersection, second truncation, tube solver); unitary and quotient volume asymptotics. Seeded, deterministic. |
| verifier_controls.py | author-verifier-controls.json | `python3 -I -B verifier_controls.py <repo> <anchor>` | Runs the AUTHOR verifier on a temporary copy under /var/tmp (deleted on exit) with 1 positive and 7 negative controls. |
| (manual run) | author-verifier-run.json | `python3 -I verify.py --anchor b6c5…beb3 --repo <repo>` in the author packet | The read-only author verifier run plus SHA256 values recomputed by the reviewer. |

Both exact_adjoint.py and finite_geometry.py were rerun before sealing, and their outputs matched the stored JSON byte for byte.

Development notes, disclosed for transparency:
- finite_geometry.py: an SVD shape mismatch was fixed with `full_matrices=False`. Coefficient-extraction conjugation/index and a K-scaling bug were fixed, after which the clean-model solver error was 6e-15. The second-truncation threshold was first crude (operator distance 0.79) and was then set to 1.5 times the actual maximal Re/Im block norm, which is the "2a with strict slack" rule of matched-volume-attempt.md G.1.
- ../verify_controls.py (controls for this packet's own verifier, output own-verifier-controls.json): the first run expected an appended review.md to fail on SHA256, but verify.py correctly fails earlier on size. The control was split into an appended-file control (expects "size") and a same-size byte-flip control (expects "sha256").
- verifier_controls.py: the expected failure reason for the altered-candidate control was first mis-specified by the reviewer; the author verifier's actual message ("payload candidate.md") is correct, and the expectation was corrected.

Limits: these are finite floating-point and exact rational checks. They do not test conjugate-variable existence, entropy limits, the order of limits, or any primary theorem.
