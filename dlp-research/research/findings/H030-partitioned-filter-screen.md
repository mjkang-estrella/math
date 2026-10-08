# H030: explicit filter guarantee exposes a paid construction cost

2026-10-08. Root construction/proof, independently checked by native Astra
/root/h007_additive_relations. Paper result only; no numerical execution or
Lean theorem. This is a conservative concrete comparator, not a new filter or
ECDLP improvement. It removes a hidden hash-independence premise from Card A.

Fix S subset Fp of b distinct abscissae, 2b<=p. Set m=2b. Independently for
each of k partitions, sample uniform a_j in Fp* and c_j in Fp, store its seed
and an initialized m-bit array. Insert x by setting position

    h_j(x)=rep(a_j*x+c_j) mod m

in EVERY partition. Query all partitions until an unset bit rejects. True
members never reject. Seed sampling/rejections, initialization and bit access
are paid; this is not a free-random-oracle assumption.

## Exact false-positive proof

For distinct x,y, affine outputs form a uniform ordered distinct field pair.
Modulo-m bucket sizes n_v are balanced. Writing p=s*m+r,0<=r<m,

    Pr(h_j(x)=h_j(y)) = sum_v n_v(n_v-1)/(p(p-1)) <= 1/m.

Indeed sum n_v²=p²/m+r(1-r/m), and
r(m-r)<=r(m-1)<=p(m-1) proves the inequality. For fixed x notin S,
union bound gives partition pass probability<=b/m=1/2. Independent seeds
across partitions give false-positive probability<=2^-k. Comparisons with
different members within one partition need not be independent.

A fixed NONMEMBER early-reject query uses at most

    sum_(j=0)^(k-1) 2^-j = 2(1-2^-k) < 2

expected partition hashes. A member uses all k; every insertion uses k.
For a fixed full-cap g-query schedule independent of seeds, expected false
resolution work<=g*2^-k*V when V bounds an unsuccessful signed resolver.
Stopping only supplies an upper bound, not an equality or variance estimate.
Seed-adaptive target/query choices need a separate argument. No claim that
an arbitrary random target shift repairs every adaptive-query guarantee.

## Space and complete-work screen

Filter storage is mk bits plus2k*ceil(log2 p) seed bits and indexing metadata.
With beta~b/log b, k=ceil(log2 log b)+O(1), log p=O(log b), filter plus a
paid exact subtable has O(b loglog b) stored bits. Choose the additive constant
in k from the actual V and desired finite false-work fraction; this asymptotic
notation alone does NOT provide a10% budget. Exact lookup comparisons, building
the subtable, full-point recovery and successful resolution still count.

Each hash above pays one Fp multiplication, one addition and bucket reduction.
Literal build therefore costs EXACTLY kb field multiplications, before baby
generation, memory initialization or seed work. At b=Theta(sqrt(q)) with
k growing like loglog b, this setup alone exceeds a constant-times-sqrt(q)
single-target field-operation baseline asymptotically. This rejects that
literal parameter/hash-cost combination as an asymptotic single-target gain.
It does not reject cheaper word hashing, other filters, smaller b, finite
constants or correctly accounted multiple-target amortization. No field M
price has been assigned to a word hash or a hardware transfer.

No numerical test is needed to establish this scoped count. A promising
replacement must name and pay its hash/layout rather than import a claimed
cuckoo/Bloom bound from the word 'universal'.

## Source boundary

Root located Carter–Wegman1979 through its publisher/IBM metadata, but fulltext
web opens of the Princeton and Masaryk hosted PDFs both returned403. The proof
above is derived here, not attributed to an unread theorem. Independent Opus
primary-source review is retained separately and does not replace this proof.
