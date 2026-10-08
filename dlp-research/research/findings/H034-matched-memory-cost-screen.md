# H034 matched peak: hash traffic and initialization tradeoff

Status: root/Sol scoped paper cost screen. Candidate retained as a hypothesis;
no complete-work win, finite benchmark or hardware measurement. This explicitly
qualifies any claim that a smaller baseline archive automatically wins by
spending spare peak on more buckets. Frozen C4-free candidate unchanged.

Let a=integral_0^3 exp(-x²)dx, f=exp(-9), b=2sqrt(2)/3. Assume the previously
reviewed moments, fresh blinded fallback, p/q->1, hash-independent stopping,
and prices under which seed setup and batch remainders are lower order.

## Capacity and exact hash expectation

Candidate and baseline records have leading width log2(p)+log2(q): exact x,
descriptor/index of half-log(q), next pointer of half-log(q), plus O(1) bits.
A head has half-log(q)+O(1) bits. With candidate3sqrt(q) records and
Hc=h sqrt(q) heads, 1<=h<2, H019 uses sqrt(2q)+o(sqrt(q)) records. Thus its
available leading head count is Hc+4(3-sqrt(2))sqrt(q). Four times Hc fits,
eight times does not. This is NOT a finite layout guarantee: compute rounded
widths, root arrays, scratch, capacities and allocator costs before any run.

For eta uniform nonzero and zeta uniform in Fp, eta*x+zeta and eta*y+zeta are
uniform ordered DISTINCT field elements whenever x!=y. Write p=kH+r. Hashing
by reduction mod H therefore has exact distinct-key collision probability

    beta(p,H)=[H*k*(k-1)+2*r*k]/[p*(p-1)] = 1/H+O(1/p).

All nonterminal prepend-and-scan queries exhaust their chains. The final query
may skip false nodes after the first exact hit, but their expected count is at
most beta E[T]=O(1). Exact-key pair coincidences at the cap have O(1) expectation
under the candidate law. Thus the earlier upper bound can be sharpened to the
same LEADING expected false-probe count in this literal implementation.

H019 uses two role tables, total Hb heads split equally, and one shared affine
hash evaluation. Only cross-role pairs are queried. There are T²/4+O(T) such
pairs, with beta(p,Hb/2)~2/Hb. Its leading second moment is E[T²]~q from the
uniform-input interleaved coverage law. Candidate E[T²]~q(1-f). Including
fresh fallback with Hb=mHc, normalized expected false-probe counts are

    candidate: (1-f)/(2h)+f/(2mh),
    baseline:  1/(2mh).

Equal total head counts give equal leading false-probe counts, despite
different mean key counts. This result does not assume independent leaf points.

## Explicit conditional weighted ledger

Each regular key costs2.5M+S+3A for coordinates, plus M+A for affine hashing.
Put gC=3.5M+S+4A+LC, gB=3.5M+S+4A+LB, Delta=LC-LB. L includes scratch/input
traffic, loop/index work, hash masking, node writes and head reads/updates.
Candidate reuses one head read for querying and insertion; split-role H019
reads its opposite-role query head and its own insertion head. Therefore
Delta>=0 is NOT established. Other differences also belong in Delta.

Let z price initializing a head and v price a false-node key read/comparison,
next-pointer read and probe-loop work. With common z,v and the same baseline
as fallback, normalized candidate minus baseline work is

    a*Delta - [(1-f)*b-a]*gB
      + z*h*[1-(1-f)*m]
      + (1-f)*v*(1-1/m)/(2h) + o(1).

Among m=1,2,4, the baseline's z*m*h+v/(2*m*h) term prefers m=1 for
v<=4*z*h², m=2 between4*z*h² and16*z*h², and m=4 above16*z*h².
These are conditional algebraic crossover inequalities, not calibrated prices.
At equal heads, the candidate's gate becomes

    [(1-f)*b-a]*gB > a*Delta + f*z*h.

The equations assume unused node payload is not initialized. Any whole-arena
initialization, allocation, release or clearing cost must be separately added;
the candidate reserves more nodes. Cache effects, variable comparison costs,
word-vs-bit models or another table layout invalidate automatic transfer of
these common weights. The baseline may use still other layouts.

If Delta>=0 and these common-cost assumptions hold, retaining equal heads
already limits possible candidate saving versus H019 to under6%. That is not
a universal no-10%-gain bound, since Delta's sign is unknown. Empirical grumpy
near0.90 leaves only about1.5% ideal key-count headroom, but its mean alone does
not supply a second moment, matched peak or complete table-cost comparison.

Decision: memory alone neither rejects the candidate nor proves its gain.
A finite diagnostic must freeze actual seed construction, table layout,
initialization, resource accounting and baseline parameters. It could check
correctness and this ledger without claiming to resolve tiny asymptotic gains.
No numerical run has been admitted or performed.

Process: root suggested second-moment comparison, exact affine-hash probability
and role-table qualification; /root/h010_early_dependencies independently
checked and completed the equations. Read-only paper review, no experiments,
imports, edits or children. Root alone integrates. No new Lean/Audit claims.
