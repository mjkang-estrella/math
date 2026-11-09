# H016 coordinator disposition

2026-10-08. **Accept the integer and restricted good-prime ideal processing
constructions after independent review. Verified full factoring complexity
improvement: NONE.**

The [construction](H016-batch-smoothness.md) and
[independent review](H016-independent-review.md) justify full sparse integer
prime exponent recovery in (B+S) poly(n), not merely smoothness recognition.
All scalar, identifier and payload widths, log B and log S must be poly(n);
otherwise retain the aggregate-bit cost. Prime-partition recursion, levelwise
product/remainder trees, exponent decoding, routing and output bits are paid.
This is a mathematical bit-cost construction using fast aggregate arithmetic,
not a claim about the speed of the Python reference or a new batch algorithm.

For monic irreducible f and primitive quadratic g of nonzero norm, good primes
p not dividing disc(f) admit ideal labels and full valuations in expected
S poly(n), or deterministic (B²+S) poly(n) with base-root preprocessing.
The reviewer checked modular degree-two splitting and bounded Hensel lifting.
For randomized splitting, a and b in aX+b are independently uniform, including
a=0. Deterministic preprocessing needs sorted joins or other paid access;
a complete table scan for each row would reintroduce an unwanted factor B.

Carry these implementation qualifications forward:

- The source PDF's smooth-part saturation condition is 2^(2^e)>=x.
- The cited small-factors Algorithm 7.1 assumes odd primes; remove 2 first if
  using that algorithm. H016's own construction handles 2 directly.
- B poly(n) memory is working scratch with discarded intermediate trees.
  Retained vectors, failures and output rows require their actual storage.
- Rejecting norms that meet disc(f) needs no factorization of the discriminant
  or global integral basis, but its effect on useful supply is unknown.
- Integer norm parity alone is insufficient: ideal labels and valuations
  remain necessary. Character evaluation is only costed for supplied verified
  labels, not for constructing a sufficient set.

The parent checked all 22 file hashes carried by the review manifest; all
matched. The reviewer independently retrieved matching primary PDFs.
No finite experiment, new shared implementation or Lean theorem was added.

H014 enumeration plus this processing removes the naive S*B upper cost.
The 1.89 per-trial envelope is still conditional: useful post-filter supply,
joint smoothness, field/character construction, useful rank, linear algebra,
algebraic square roots, denominator handling, proper gcd probability and
restarts are unpaid or unproved. H017/H019 and H018/H020 address supply.
Do not call removal of an implementation cost a full factoring improvement.
