# H028 paid chained-table contract

2026-10-08. Root proposed prepend-every-record buckets; native Astra and Sol
independently validated expected visits, sampling, storage and baseline caveats.
Paper contract only, not an implemented full solver or verified improvement.

Use two tables with a common bucket count H, 1<=H<=p. A table has H head
pointers and append-only records (full canonical key, progression index, next).
Zero pointer denotes null; records are addressed by positive indices. Actual
EC infinity is dispatched before lookup. Ordinary finite h=0 is retained.
Each new record queries the opposite table first, then prepends to its own
bucket without a same-side search. Compare exact keys before attempting the
two archive-free scalar verifications. Keep every record, including duplicates.
Each cross-table record pair is visited at most once, when the later arrives.
Full deterministic coverage streams and their geometry are fixed independently
of hashing; stopping can only remove visits from the full streams.

## Concrete hash and proof

Sample a uniformly from Fp* and b uniformly from Fp, independently of the EC
blinding. With canonical representative x in [0,p), compute

    slot(x) = ((a*x+b) mod p) mod H.

The first modulus is field multiplication/addition; the second is integer
remainder and is separately charged. Hash once per generated key, reusing its
slot for opposite query and own insertion. Uniform rejection sampling and failed
draws are paid. Fixed finite PRNG seeds do not establish the ideal uniform law.

For distinct x,y, (a*x+b,a*y+b) is uniformly distributed over ordered distinct
field elements. The residue-mod-H bins have balanced sizes L_t. Thus

    epsilon = sum_t L_t(L_t-1)/(p(p-1)) <= 1/H.

One elementary bound fixes the first output: at most ceil(p/H)-1 second outputs
share its bin. H*(ceil(p/H)-1)<=p-1 proves the inequality. No random-map or
same-side key independence assumption occurs. Astra independently reviewed the
alternative floor(H*u/p) bucket map; it has the same balanced-bin proof but
requires integer multiplication/division. We choose remainder here and do NOT
silently charge the alternative's operations or treat either map as free.

For fixed full nonidentity record caps I,J, independent paid EC randomization
and the accepted H028 fibre theorem give

    E bucket-record visits <= IJ/H + 6IJ/q,
    E scalar verification multiplications <= 12IJ/q.

The first inequality overcounts unequal-key hash collisions by IJ/H and then
adds all exact-key cross matches. This is a sufficient upper bound, not a
necessary observed cost. The proof does not need the progression duplicate
lemma: prepend performs no same-side comparisons. That lemma remains useful
for alternative layouts, but is not manufactured into an iid hypothesis.

With I,J,H=Theta(sqrt(q)), table visits, initialization and generated hashes are
expected O(sqrt(q)) under the stated arithmetic-operation model. Hash arithmetic,
integer operations and bit widths remain part of complete cost. This is not an
O(sqrt(q)) binary-step theorem or a deterministic verification-work guarantee.

## Explicit accounting vector

For N inserted records and V bucket visits, with all fixed-cap allocation paid:
- 2H head initialization writes, plus allocation/zeroing actually performed.
- N field M, N field A, N integer remainders for hashing; paid seed sampling.
- N opposite-head reads and N own-head reads/writes.
- 3N record-field writes (key/index/next), plus capacity initialization if any.
- Per visit: key read, exact comparison, next read, loop/control/index work.
- Per exact match: scalar index read, modular label arithmetic and up to two
  full verification scalar multiplications; stop only at verified success.
- All labels, counters, bounds checks, exceptional point dispatch, terminal
  complete-block generation and actual startup are retained separately.

No numerical run or price assignment is implicit in this vector. Resizing is
not used in this fixed-cap contract; a dynamic replacement requires its own
charged allocation and rehashing analysis. Early success still pays full initial
head arrays; it does not retroactively remove startup.

Let b=ceil(log2 p), w_i hold the largest stored progression index, and w_n hold
capacity plus null. Record payload is b+w_i+w_n bits; add 2H head pointers,
active full points/h states, hash state, capacity slack, alignment and allocator
metadata. Packing index and next requires a demonstrated width bound and paid
packing/access. Semantic fields are not automatically physical words.

## Finite admission and comparator fairness

A competent exact-x comparator may use open addressing and retain one index
per exact key. Do not force it to adopt chaining, keep every duplicate or do
candidate-only generator randomization. Likewise do not automatically charge
a shared hash multiplication only to h. Compare actual chosen implementations.

For k=ell=8, S/M=4/5,I/M=8 and zero prices for all other work, the regular x
kernel costs2569/680 M/key and the candidate saves64/85 M/key. Including this
hash's1M as common work yields x cost3249/680, so the remaining optimistic
10% margin becomes

    64/85 - (1/10)*(3249/680) = 1871/6800 M/key.

Root/Sol checked the exact arithmetic. Field additions, canonical comparison,
integer remainder, common memory work, candidate extra traffic, initialization,
verification and stopping differences further affect the margin. This is not a
physical measurement or a proof that the margin is met. If the baseline uses a
cheaper hash, its actual cost must replace this illustrative shared choice.

The current contract closes a correctness/expected-work gap; it leaves the
complete-cost gate unresolved. H028 retains square-root memory and exponent;
no saving is established for memory-light rho, whose next step needs the full
point. For full prime-order curves q is close to p, so small-q experiments do
not secretly exercise large-p field arithmetic. Synthetic finite results cannot
establish full-size practical feasibility. Verified complete-work gain NONE.

## Complete expected-cost condition (Sol final review)

For a common expected generated-key count K justified by the separate paid
uniform blinding laws (not identical trial stopping times), let b_x be the
complete baseline regular cost/key and C_x its other expected cost. Define

    d = [2ell/(2ell+1)]s - [3(ell+1)/(2ell+1)]a - c - DeltaL.

Here a is field-addition/M and c canonical-comparison/M. Let DeltaC be a justified
upper ledger for candidate-minus-baseline setup, exceptional, overshoot and
verification work. Then a sufficient epsilon-saving condition is

    K*(d-epsilon*b_x) >= DeltaC + epsilon*C_x.

All differences and common work require matched definitions. Failure of a
sufficient upper-ledger inequality does NOT prove the candidate loses. Necessary
rejection needs unavoidable lower costs exceeding maximum possible credit, as
in the first diagnostic's actual Miller-setup loss. The separate scalar/index,
RAM and bit ledgers cannot be dropped when calling a result complete work.

Final native Sol review COMPLETED and recommends a bounded stopped-solver test
only after a reviewed size/setup/overshoot and implementation contract leaves
positive headroom. No new numerical run is currently admitted by this paper.
