# W009 reciprocal law — parent disposition and review repairs

2026-10-08. Exact identities **accepted**; several review extrapolations
**rejected or restricted**. Verified factoring complexity improvement: NONE.

The [Opus review](W009-reciprocal-review.md) validates displayed formulas
(1)–(5), both subgroup formulas, and the trace counts. The parent verified
all nine frozen input hashes and recorded the terminal payload hashes in
[an intake manifest](W009-reciprocal-intake-manifest.json); the child did
not supply the requested delivery manifest. Its 71 certificate checks are
retained, including fixed F_5/F_7/F_13 examples. These are algebra checks,
not factoring experiments. The later simple-pole proof is a separate audit.

Accepted clarifications:

- Infinity is individually absorbing; zero maps there on the next update.
  The original note said this correctly; the parent's B task incorrectly
  described both colors as individually nonabsorbing.
- Uniform affine input already realizes the flat full subgroup. The large-m
  one-step gain is not an additional source of favorable input. Small
  subgroups m=2,3,4 contract residual collision mass, consistently with the
  formulas; the original note's near-doubling claim was for large m only.
- Relative to gcd(V,N), adding gcd(U,N) contributes precisely
  z_p*r_q+z_q*r_p. Relative to gcd(U*V,N), separate tests recover the
  opposite-color events z_p*h_q+h_p*z_q. The original note used this
  second comparison; it did not claim a numerator test is needed for
  zero-versus-pole when the denominator is already tested.
- Training evaluations already supply factor-test opportunities. Their
  gcds and evaluations still cost work; using them as probes does not
  make all failed charts useless or retries free.
- At ell2=0 use raw truncated moments, not conditional expectations.
  The parent's new fixed raw-attempt/no-op protocol supplies a finite cap.
  General retries use the C,R,J outcome ledger from the pinned disposition.

The following review conclusions are not supported:

1. **One planted pair does not prohibit large zero mass.** Its two fibers
   may be heavy. The exact bound z_new<=2*max(nu) is useful only with a
   bound on max(nu). A concrete local example is p=5 and F(z)=z-1/z.
   Uniform affine input gives outputs (infinity,0,-1,1,0) at inputs
   (0,1,2,3,4). The legal second anchors 1,-1 give F composed with F,
   whose masses are z=2/5, h=3/5 and no residual mass. Both anchors have
   positive sampling probability. This is a reachable nonconstant two-color
   partition, contradicting the review's purported structural impossibility.
   It is a finite algebraic counterexample, not an asymptotic gain or a
   benchmark input after fixed small-prime removal. At the next stage the
   local clean probability is zero; useful gcd opportunities may remain.

2. **The stated 1/p^2 frame-alignment probability is unproved.** For fixed
   r^2=c, the exact identity is

       (z+c/z-2r)/(z+c/z+2r)=((z-r)/(z+r))^2.

   Newton_c(z)=(z+c/z)/2 is dynamically conjugate to squaring. The
   translated fold has different input and output Möbius frames. Matching
   the displayed unordered frames for the next fold requires y+w=0 and
   c_next=4c. This is a valid condition for that particular alignment,
   not a classification of every structured composition. Its probability
   depends on the current weighted output law and parameter policy.
   An odd current map can obtain opposite anchors deterministically by
   evaluating r and -r; the [odd-pair note](W009-odd-paired-fold.md) makes
   that changed computation explicit. No independence/uniformity argument
   for 1/p^2 was supplied. The abstracts cited by the review do not prove it.

3. **Full local status vectors do not generally describe a stopped chart.**
   Under first-failure stopping, matching an early failed check returns gcd N
   even if a later hypothetical check would separate the primes. Use the
   first-failing-check labels from the pinned audit. A complete status-vector
   formula needs a different, fully specified policy, including how checks
   involving unavailable affine inverses are handled.

The precise survivor is the executable reciprocal sampler and its squared
multiplicative-energy law. Persistence is still the hard part. The parent's
[simple-pole derivation](W009-simple-pole-envelope.md) proposes a uniform
early-depth limit, not an all-depth impossibility or an actual-work bound.
Do not adopt the child review's broad closures in place of that argument.
