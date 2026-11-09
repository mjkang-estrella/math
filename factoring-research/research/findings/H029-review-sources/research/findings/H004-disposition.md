# H004 disposition: retain reduction, reject power-shift construction

Verified factoring complexity improvement: **NONE**.

The [independent review](H004-reduction-review.md) accepts the prime-cover
reduction with costed construction, modular interval products for every divisor
up to N, and an executable leaf factor routine. This is an interface weakening
implicit in the existing Umans–Wang proof, not a new algorithmic bound. Stripping
all multiplicities from the original N is necessary; dividing only by the root
gcd can leave a composite remainder. The reviewer checked 9,520 partition cases
and 3,076 tiny factorizations; these are correctness diagnostics.

The [construction attempt](../hypotheses/H004-prime-cover-construction.md)
tested differences `2^e+1,...,2^e+m^2`, with R=m³. All 14 nominal choices
`e=2m` failed coverage. The registered tuning grid succeeded only at m=2;
all 339 exponents at the other nine sizes failed. All 360 total cases finished,
and complete missed-prime lists, source and hashes are retained beside the
report. For N=3599, the nominal interval 257,...,272 misses both 59 and 61.

Cheap product evaluation cannot compensate for missing coverage. Even with
coverage, a leaf may contain both factors, so gcd descent does not supply a
cheap unrestricted leaf factorer. Explicitly listing all required primes or
all prefactored leaves has an output-size obstruction at the target scale.

Close this construction. The suggested two-sided power-shift revision repairs
a particular residue-one failure but supplies neither general coverage nor a
leaf routine. Do not run an enlarged shift grid merely to fit these examples.
Reopen this branch for an analytic cover construction with a new coverage or
leaf-separation mechanism and a total bound below the matched baseline.

