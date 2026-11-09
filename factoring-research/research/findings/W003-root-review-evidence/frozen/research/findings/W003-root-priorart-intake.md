# W003 Lens B — coordinator intake

2026-10-08. **UNACCEPTED pending independent review.**
Verified COMPLETE factoring complexity improvement: **NONE**.

The coordinator consumed all 572 lines of
[the source/reduction submission](W003-root-inversion-priorart.md), its
input inventory and source/access ledger. The task is completed with no
pending child runs. Its original remains unchanged; the byte-identical
[submitted snapshot](W003-root-priorart-submitted-draft.md) has SHA-256
2053748929ba399bf4e010fc0133ce12cd60d4c568745a44b06ae7a6c788f275.
All 19 frozen input files, 23 source identities and 54 original delivery
entries verified. The unchanged W003 brief has SHA-256
fc8f5cf42a34b020833832a56994421c183e22a8fd2e951a6cb9c6cee14ab629.
Hash verification does not validate any mathematical claim.

The coordinator separately reopened Dixon's primary PDF and the Rabin MIT
metadata record, read Dixon's archived smooth-square/fiber passage, and
visually inspected the submitted Dixon images of printed pp.257 and 259.
Those pages support the historical theorem's conservative 3sqrt(2) constant
and the supply estimate invoked here. This intake is not a fresh full-proof
audit of Dixon or the other primary sources.

## Submitted deductions and claimed scope

The report distinguishes Rabin's root-inversion reduction, Dixon's proved
integer smooth-square method, Lenstra-Pomerance's better rigorous complete
bound, conditional useful output in randomized NFS, and existing two-field
selection and field-root reconstruction. The report explicitly limits each
source inspection and records failed retrievals.

For odd N with k>=2 distinct prime factors, a valid inner root depending only
on N,R and independent tape leaves exactly 2^k possible outer preimages.
Exactly two are globally +/- the returned root. The new raw-word accounting
includes proper initial gcds, out-of-range words, zero, early inner factors,
root failure and retries. Its exact probability and C_N/p_N identity require
checking under stopping and prime-power multiplicities.

The concrete integer adaptation samples independent epsilon and an n-bit
word m, forms v=R^epsilon m^2 mod N on units, and retains positive B-smooth
representatives. B lies between v_0 and 2v_0, where
v_0=exp(sqrt(2 log N log log N)); h is the prime count up to B.
The cap is T=ceil(16(h+1)B). A dependency from h+1 smooth rows is chosen
without inspecting m or epsilon. For a proof-only root h_R, multiplication
m -> h_R^epsilon m supplies a coupling to Dixon's squared-residue law.
The selected nonzero dependency has odd epsilon sum with probability 1/2.
For odd E, S/M/R^((E-1)/2) is the proposed root.

The claimed supply and cap yield probability greater than 3/8 of FACTOR or
ROOT for all sufficiently large continuing inputs. The conservative dense
realization costs B^3 poly(n) time and B^2 poly(n) space, leading to complete
expected L_N[1/2,3sqrt(2)] factoring. This is slower than the inspected
Lenstra-Pomerance bound and is not an advance. The integer coupling does not
transfer to the W003 two-field law.

The report also supplies square-class target membership, an explicit costly
subset-search fallback, derivative-cleared mixed-field reconstruction,
the necessary relative-norm condition that -1 be a norm, its negative-real-
embedding obstruction, and the invariant/anti-invariant bit left after
squaring in a quadratic extension. These are new submitted deductions here
with no underlying-algebra novelty claim.

## Independent-review obligations and unresolved questions

1. Verify the raw-word probability formula and recurrence for cold expected
   work; handle repeated prime factors, preprocessing, fixed caps, invalid
   outputs, and all-input recursion. Distinguish an inner factor from a root.
2. Prove the twist coupling for the entire stopped experiment, not just a
   one-row marginal: rejected words, gcd outcomes, retained exponents, row
   order, completion, and the chosen dependency. Check independence of the
   retained labels after conditioning on no early success. No hidden root
   may be computed by the actual algorithm.
3. Match the uniform smooth-square bound to Dixon's exact hypotheses and
   verify its transfer from v_0 to rounded B. Supply a finite paid certified
   parameter-rounding procedure if the prose leaves one implicit; no exact
   real-number or unknowable threshold oracle is allowed.
4. Check the binomial/Chebyshev inequality, early-factor handling, strict
   constant lower bound, small-input positive success and combination with
   the outer law. In particular, justify every conditioning used in turning
   the hypothetical full tape into a stopped successful trial.
5. Give a finite sequential-tape schedule if needed to substantiate the
   stated cubic dense cost, including ordered pivots, provenance, full
   exponents, prime-list scans, random bits, reconstruction and all widths.
   An unnoticed extra power of h changes the L constant and must be fixed
   or disclosed. Verify the ROOT-only wrapper and factor-tree accounting.
6. Audit the field-square fallback, its variable degree/height cost, the
   derivative order multiplier, monic/nonmonic conversions, square alpha,
   and every zero/nonunit/full-gcd branch. Confirm the norm and involution
   claims and their scope without assuming a norm-equation oracle.
7. Check each primary theorem/algorithm used for a quantitative or scope
   claim. Preserve the source ledger's failures and limited read scopes.
   Lenstra-Pomerance's opening theorem is not a whole-proof audit; Nguyen's
   fixed-field empirical behavior is not a variable-degree root theorem.
8. Assess the precise small-R counting bound and the absence of an actual
   coupling to the modified NFS generator. A bounded literature search
   cannot establish nonexistence. Lens A is not independently reviewed by
   this source task, even where its provisional sign observation agrees.

No correctness defect is established by this initial read. These are
verification obligations rather than accepted results or author responses.
No experiments or Lean work are selected. A prescribed-target method with
subexponential NFS-scale costs and proved completion mass remains missing.
