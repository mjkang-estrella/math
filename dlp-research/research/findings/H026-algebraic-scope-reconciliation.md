# H026 algebraic proposals: scope reconciliation

2026-10-08. Supersedes the broad rejection statements in H026-algebraic-opus-raw.md.
Initial Claude Opus5.5 proposals were independently reviewed by native Astra
(/root/h007_additive_relations, C1/C2 and comparator) and native Sol
(/root/h010_early_dependencies, C3–C5). Root integrated and checked the logical
distinctions below. Neither reviewer ran experiments or edited files. No new
algorithm, Lean theorem or complete-work improvement is claimed.

## C1: literal expanded-character relation search

An exact order-n multiplicative character requires n dividing p−1. Exclude x=0
and infinity from a nonzero character fiber. The heuristic density gives B≈q/n;
2(p−1)/n is only an elementary upper bound, not the expected size. Concentration
needs a separate estimate. Assuming n≈q/B, n^m individually processed character
terms per query, and the proposed relation/rank plus B² linear algebra ledger,
the optimistic work is at least of order

`q^(m+1)/B^(2m−1) + B²`.

Balancing gives B=q^((m+1)/(2m+1)) and exponent 2(m+1)/(2m+1)>1. This rejects
the literal expansion even under its optimistic ledger. At this balance B^m≫q;
the claimed B*m!*q/B^m queries are fewer than B, so cannot collect B rows from
one-witness queries. Such a collector needs B*max(1,m!*q/B^m) queries, unless
multiwitness extraction is supplied and charged. This is not an executable
upper bound based solely on expected representation counts.

A cyclic-cover point count sums character components, not an arbitrary individual
character sum. For the generic pair cover, at most six geometric divisor support
places and tame connected degree n give
`2g−2 = sum_P (n−gcd(n,v_P(h)))`, hence g≤3n−2. Degeneracies/disconnected cases
need separate treatment. Neither genus nor expanded-term count proves a general
point-counting runtime lower bound. Restricted counting and witness extraction
remain the missing operations; arbitrary factor-base halves need not preserve
a cheap character description.

The tabulated (m−1)-sum comparator is conditional, for fixed m≥3: storing
unordered distinct sums costs about B^(m−1)/(m−1)! witness records, a target scans
B last points, and assumed useful-row probability min(1,B^m/(m!q)) plus Θ(B)
useful rows gives sparse-regime work
`a_m B^(m−1)+b_m q/B^(m−2)+B²`.
The balance B=q^(1/(2m−3)) has exponent (m−1)/(2m−3). Success, rank, signs,
duplicates, extraction, base construction and factorials remain assumptions or
costs. This is not a universal best algorithm, and growing m needs new analysis.

## C2: cyclic surface quotient

The map (P,R)↦(P,R−[k]P) sends the graph subgroup to <(G,O)>, but uses unknown k.
When E(Fp)=<G>, 1−Frobenius has that kernel, giving an unpolarized existence
isomorphism of the quotient with E², not executable scalar recovery.

Polarization and marking must be specified. A cyclic degree-q surface quotient
is not automatically a principally polarized q-isogeny. If a descended
polarization pulls back to q times the product polarization, its degree is q²,
not one. Source automorphisms give some equivalences, not uniqueness up to
±k,±1/k; ordinary j=0 curves can have extra automorphisms.

Astra read Robert's full author-hosted paper, including its principally polarized
N-isogeny convention of degree N^g and elliptic input distinctions (kernel
polynomial versus rational generator). These do not support the raw cyclic
surface cost claim. Source:
https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/articles/polylog_isogenies.pdf

Universal q-evaluation inversion and torsion-field construction lower bounds
are withdrawn. Needed: a specified computable invariant, scalar distinguishability,
constructive inversion, and charged setup/memory. No such primitive is supplied.

## C3: modular parametrization

The generic-conductor objection is withdrawn. A fixed rational elliptic curve
has fixed conductor and can have good reductions meeting the challenge; this
does not claim infinitely many prime-order reductions. A memory-based p^(6/5)
conductor heuristic cannot reject these inputs or prove a runtime lower bound.
Normalized Hecke-equivariance can give relations under its actual reduction,
correspondence, multiplicity and cusp assumptions. The outputs still mostly
have unknown logs. No paid known-log closure, useful rank or recovery method
was supplied. Need an explicit supplied-curve map, preimages and full ledger.
Sol inspected official Sage modular-parametrization documentation; this is
interface evidence, not a theorem for an attack:
https://doc.sagemath.org/html/en/reference/arithmetic_curves/sage/schemes/elliptic_curves/modular_parametrization.html

## C4: elliptic basis and traces

Sol read Couveignes–Lercier §§2–3.1, Lemma1 and equations8–9:
https://www.math.u-bordeaux.fr/~jcouveig/publi/ellbasisrev.pdf
With pi(b)=b+G and qb≠O, omega_0=1 and omega_j=u_(O,jG)(b) form the stated
basis. This Omega basis is not normal: Frobenius has correction constants.
The paper's separate adjacent-function Theta basis supplies normal conjugacy.

For trace-dual omega_j*, c_l=sum_j bit_l(j)omega_j* satisfies
Tr(c_l omega_k)=bit_l(k). For Q=kG≠O, u_(O,Q)(b)=omega_k. This is an identity,
not a cheap decoder: b, c_l, the extension and trace all require paid construction.
A rational-function representation C(b) allows a pushforward along 1−pi under
regularity conditions. Constant pushforwards may depend on j; the raw assertion
that all traces must coincide is false. Riemann–Roch dimension is not a circuit
or degree lower bound for the particular c_l.

The paper's §4 fast-arithmetic interpolation additionally asks for rational R
with qR≠O; none exists if the entire rational group has order q. This limits that
setup, not basis existence. A repair over an extension must be charged.

## C5: dual-number tangent lifts

For a constant smooth curve over Fp[epsilon], the group splits into its constant
section and tangent part. Thus [k](G,v)=(kG,(k mod p)v). A public nonzero tangent
lift of Q=(x,y) is easy, for example
`(x+epsilon*2y*v, y+epsilon*(3x²+A)*v)`.
The missing information is compatibility v_Q=(k mod p)v_G, not existence of
lifts. For q≠p a nonzero-tangent lift of G has order pq and depends on the integer
representative, rather than only k mod q. Every group-homomorphic section of
the q-subgroup has zero tangent component since Hom(Z/q,Z/p)=0.

## Decision

Reject the literal C1 expansion; retain C2–C4 as missing constructive primitives,
and C5 as a compatibility barrier for the stated lift method. None merits a
numerical run as supplied. These are scoped negatives, not universal exclusions
of coordinate-aware algorithms. Best supported complete work remains square-root;
verified improvement NONE. No hardware extrapolation or generic proof work.
