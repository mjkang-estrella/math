# W005 — blinded Norm2 sampler accepted at its joint-wrapper scope

Date: 2026-10-08. Verified new improvement over established factoring: **NONE**.

The parent consumed the complete [independent review](W005-blindnorm-review.md)
and accepts its equal-fiber proof, prime-power coverage, exact capped law,
strict inner-interface independence, W004 extraction transfer and conservative
complete expected reference bound. No algebraic repair is required.
The [original proposal](W005-blinded-norm2.md), frozen protocol, evaluator and
first-run evidence remain unchanged. These are reviewed mathematical arguments,
not a new Lean proof or a implemented complete factoring wrapper.

The saved computation is concrete: replace construction, sorting and merging of
two N-record Norm2 lists and O(N log N) storage with the explicitly capped
homogeneous-pair sampler. Its bit work is polynomial, conservatively O(n^6),
and its streaming scratch space is O(n), where n=bitlength(N). This is valid
because the OUTER factoring trial knows the random x used to form R=x^2;
there is no faster standalone N,R-only Norm2 theorem here.

Adopt the review's exact stopped law. If s is coordinate-entry probability,
alpha is the unit-norm pair probability, beta is proper-gcd probability,
delta=1-s(alpha+beta), and B=2(n+1)^3, then

    C_B = alpha/(alpha+beta)*(1-delta^B),
    F_B = beta/(alpha+beta)*(1-delta^B),
    E_B = delta^B <= exp(-(n+1)).

The last bound concerns factor-or-certificate termination, not certificate
probability alone. All raw-word and pair-cap failures remain failures.
Uniformity is conditional on the certificate branch.

The inner procedure may receive N,R,u,v and fresh independent randomness.
It must not receive x, the accepted pair/rotation, its reconstructible seed
or intermediate inverse trace. An x-independent predicate on accepted pairs
is NOT by itself safe: keeping only b=0 destroys the uniform-group law.
The affine-only chart is likewise insufficient over composite rings.
Postprocessing depending only on permitted inner inputs preserves independence,
but must still have its actual work and failure probability charged.

The raw outer success identity uses the NEW uniform-certificate distribution,
including the new factor and exhaustion probabilities. It does not retain
the old deterministic selector law or assert useful packet mass. Only the old
nonunit-x gcd branch is needed for the conservative complete expected bound
O(sqrt(N_0) poly(log N_0)), with paid primality termination and recursion.
This improves the old W004 reference upper envelope O(N_0^(3/2) polylog N_0).
It does not beat trial division or establish a matching lower bound or timing
ratio for either reference.

The authorized finite screen had 8 PASS, 0 REJECT, 0 UNKNOWN across 62,504
enumerated pairs. Both dependence controls failed as expected in every case.
All cases completed within their frozen limits; the recorded total was
0.960133 seconds and peak Python traced allocation 259,914 bytes. This tests
the listed finite maps, not the caps, asymptotic cost or factoring success.
The reviewer ran the required project checks: 12 Python tests, source screen,
pinned Lean build and existing audit passed. No shared solver or Lean source
changed. The parent independently verified all 39 delivery hashes.

The norm-one/Hilbert-90 construction and root-to-factor argument have established
prior art; exact priority was not resolved by the bounded source search.
Source scope and failed endpoints remain recorded, without repeated retrieval.

**Next constructive question:** exploit this cheap, root-choice-independent
input stream with a fully priced useful-root computation. The parent's
[compatible-field construction](W005-compatible-field.md) is a separate
provisional attempt to remove the second-field square search; its modular
constraint and root coupling are under a new independent review.
