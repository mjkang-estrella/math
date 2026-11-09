# H025 — Coordinator disposition

2026-10-08. **ACCEPT after the fixed-power-saving wording correction and
acceptance of H024's exact diagonal count.**
Verified full factoring complexity improvement: **NONE**.

The coordinator read all 308 lines of the [independent review](H025-independent-review.md).
It accepted the finite-universe lemma and explicit cutoff independently, and
the density consequences conditional on H024's count. That exact count
M_k(E)<=exp(11E^(1/3)) has now passed H024's separate independent review;
[H024 disposition](H024-disposition.md) records acceptance. The interfaces
match: both count diagonal energy with weights ceil(j/2), not merely an
N-dependent rounded sublevel set.

The [submitted draft](H025-submitted-draft.md) is preserved byte-for-byte,
SHA256 `4bcd2ebcfb0cf6dba710a83172656da6597842db4bfea99c4bb1ef68e8b95b5c`.
Review SHA256:
`4566d18e8f62e33c651183f2f7735ec9df61951ece0345b3ab9157862f27f56c`.
The review used H024's original bytes, also preserved in that review's source
snapshot. Later H024 edits clarified accepted status and probability scope;
they did not change the diagonal count.

## Accepted result

For fixed bit length ell, prime list and weights, every vector fixes positive
integers u,v. The inequality |u-Nv|<=W holds for at most floor(2W/v)+1 integer
inputs. Union over the entire diagonal universe gives the exact finite
upper count, irrespective of an algorithm's selection after seeing N.

H024's cheap cutoff obeys E_star<40ell² uniformly. With
K=11*40^(1/3), for each fixed 0<epsilon<1 the fraction of ell-bit inputs
admitting any allowed vector with |u-Nv|<=N^(1-epsilon) is at most

    min(1, exp(K ell^(2/3))
                   *[4*2^(-epsilon ell)+2^(1-ell)]),

which tends to zero. No smoothness or arithmetic-randomness premise is used.
The general finite window count, subexponential windows, E_bar=o(ell³)
consequence, maximum-point-mass bound and restricted-set normalization are
accepted with the report's explicit conditions.

## Required wording fix and limits

The original section 4 said “sublinear-in-N,” which could mean every o(N)
window. That conclusion is unsupported: inserting N/ell into the available
bound gives an eventually uninformative value after clipping. The corrected
[report](H025-small-residual-density.md) now states only the proved
fixed-epsilon power saving, and explicitly excludes the stronger reading.
No equation needed alteration.

This is a density theorem for a fixed generator universe, not an all-input
factoring lower bound. Exceptional inputs remain possible. Large residuals
may still be smooth and useful; rank, square roots and proper splitting
remain unproved. No balanced-semiprime density assertion follows without
the restricted input-set size bound. N-dependent bases or weight assignments
need a separately controlled union of universes.

For E_bar=c ell³, the estimate can still decay when c is sufficiently small;
energy of that order alone establishes neither decay nor useful supply.
Increasing a polynomial energy cutoff can retain polynomial optimization
ranges, but selecting tiny actual residuals remains a separate costed task.

## Next research direction

A proposed escape must specify a costed selector at a sufficiently larger
energy, a different controlled prime/weight universe, or a justified useful
distribution at larger residual sizes. The accepted count supplies no such
mechanism. H023's independent geometry/special-form review remains active
and is a separate branch.

No code, finite experiment, package or Lean changed. Shared checks were not
repeated for document edits. No new full factoring complexity improvement.
