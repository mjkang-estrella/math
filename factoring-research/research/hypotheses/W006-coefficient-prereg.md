# W006 A — preregistered cyclic-binomial primitive screen

Frozen before candidate execution, 2026-10-08. This authorizes one bounded
standard-library screen only; no shared solver/harness or Lean changes.

Inputs in fixed order:
77, 143, 221, 437, 899, 1763, 2701, 3599, 49, 121, 97, 127.
Degrees in fixed order for each input: 2,4,8,16.
The first eight are balanced semiprime research inputs; next two prime powers;
last two prime controls. Labels and factors are evaluator-only. Candidate
receives N,L only. No seeds or adaptive degree expansion. No reruns.

Candidate: compute (1+X)^(N-1) modulo X^L-1 with coefficients modulo N,
using binary exponentiation and schoolbook cyclic convolution; reduce each
multiply-add modulo N. Count every coefficient multiply-add, even zeros.
Record exponentiation steps, all coefficient residues and gcds, maximum
operand width, elapsed time, traced allocation, and stop reason.
Return only a checked proper gcd, otherwise NO_FACTOR or UNKNOWN on a cap.
Every tested gcd is retained; no data-dependent extra transforms are allowed.

Controls: evaluator independently computes exact math.comb(N-1,(N-1)//2)
and its gcd, retaining its width and work time separately. It also computes
all exact row coefficients by the integer recurrence and folds them, to
verify the cyclic vector. This is tiny-corpus control work, not a promised
efficient implementation. The known factors may verify the predicted A1
outcome but never enter the candidate.

Budgets: 60 seconds whole screen including setup/control work, 1 second
per (N,L) attempt including controls, 20,000 coefficient multiply-adds per
attempt, soft 32 MiB traced allocation, 1 MiB evidence per attempt, 16 MiB
total. Timed-out, failed or unstarted attempts remain UNKNOWN; do not remove
them from denominators or raise caps. Check time during arithmetic and
control recurrences. A hard separate process timeout may enforce the whole
cap. Freeze source and protocol hashes before the only execution.

Acceptance/rejection: any vector/control mismatch or invalid factor rejects
the implementation. One balanced input with NO_FACTOR at every menu degree
rejects pointwise coverage for this fixed menu. Report exact successes and
failures by degree and input; do not infer a general probability or exponent.
Prime/prime-power behavior is diagnostic outside A1's promise. Validate the
central-coefficient control against A1 on every promised input.

Exclusive child prefix research/findings/W006-coefficient-validation-,
with report research/findings/W006-coefficient-validation.md. Preserve JSON
outcomes, frozen source/protocol and bounded read/source scope. Run
scripts/check.sh after writing scratch code, separately from the screen cap.
No reruns or expanded search follow a failed folding hypothesis automatically.
