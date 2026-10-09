# H043 modular resultant repair; no complete solver gain

2026-10-09 UTC. Factory Opus's terminal report is retained verbatim in
H043-structured-system-factory-raw.md, including its task ID. Root integrated
independent native Astra mathematical and Sol cost reviews. The raw blanket
rejections are not accepted. Best supported exponent remains 1/2; verified
complete-work improvement NONE. No executable experiment, new Lean claim or
H034 cap reset. The conclusions below are paper arguments, not Lean theorems.

## B: evaluate the remainder, not the full resultant

Let F(Y)=a(X)Y²+b(X)Y+c(X), g(Y)=Y^u−1, u≥1. Set

    s_0=2, s_1=−b, s_j=−b*s_(j−1)−a*c*s_(j−2).
    Res_Y(g,F)=a^u+c^u−s_u.

Proof: for generic roots r1,r2 of F, the resultant is
a^u(r1^u−1)(r2^u−1)=c^u+a^u−a^u(r1^u+r2^u).
The scaled roots a*r1,a*r2 have sum −b and product ac, giving the stated
recurrence. This is a polynomial identity in a,b,c, so it specializes even
when a vanishes. Since g is monic, no leading-coefficient division is needed.
For u=1 the result is a+b+c; for u=2 it is (a+c)²−b²; for a=0 it is
c^u−(−b)^u, the correct linear-polynomial resultant.

For a list polynomial L of degree n, do every operation in R=Fp[X]/L.
The matrix [[−b,−ac],[1,0]] has trace of its u-th power equal to s_u.
Binary powering this matrix and a,c takes O(log u) ring multiplications,
including in a quotient with zero divisors. With fast polynomial arithmetic,
this costs O(M(n) log u) field operations, or soft-O(n log u). A gcd with L
then detects its common abscissae with the resultant. Constructing the
degree-2u polynomial is unnecessary. This is a standard norm/Lucas identity
applied modulo L, not a claimed new attack or novelty result.

Applied to S3(x(P),X,Y), this repairs the named torus-filter reporter. Require
u|(p−1) for the specified rational subgroup mu_u; a divisor of the desired
size is not guaranteed on arbitrary prime fields. Use distinct abscissae in
L, retaining all signed records behind duplicates. Locate gcd roots in the
stored list by paid evaluation; compute actual signed point sums and check
finite abscissa membership to retain labelled witnesses. Infinity, equal
abscissae, leading-degree drops and other exceptional branches need dispatch.
These checks prevent interpreting an algebraic root as a valid labelled
relation without verification.

n queries now have a soft-O(n² log u) field-work implementation rather than
the raw compulsory n*u invoice. At n=q^(1/3) this schedule has roughly q^(2/3)
modeled field work: it does not establish sub-square-root work. An upper
estimate is not a lower bound on all reporters. List generation, product-tree
setup/storage, gcd-to-index extraction, sign/witness recovery, second-level
matching, null scalar coefficients, restarts and final verification remain
paid. Up to n² pairs can be reported; output-sensitive bounds require an
actual output law or bound. Sequential processing can discard query temporaries;
retaining all outputs may instead dominate memory. No hardware time is inferred.

The actionable opening is now precise: a changed shared-query or sparse-output
operation with full witness extraction could improve this schedule. Merely
renaming a resultant, ignoring extraction, or assuming polylogarithmic reporting
does not provide it. No numerical trial is admitted from this correction alone.

## A: a presentation-specific degree count, not a solver lower bound

For independent coordinate constraints f_i(x_i)=0 with B distinct roots each,
the first m−1 constraints in m-space cut out B^(m−1) affine lines. Their
degree is B^(m−1). This exact direct-order count does not prove the same
intermediate degree for every lifted system, equation order or generic linear
combination. A degree-dependent runtime upper bound is not a runtime floor.

Root read [Cafure–Matera's introduction and Corollary 6.4](https://arxiv.org/pdf/math/0406085).
Their hypotheses include a regular sequence, radical prefixes and absolute
irreducibility of the final variety. The field condition is p>8N²d*delta_r^4,
where delta_r is the FINAL degree; complexity uses delta=max_s deg(V_s).
These parameters were conflated in the raw report. A large intermediate
degree alone does not violate the stated field condition. The paper also
computes zero-dimensional fibers, so that phrase alone does not exclude its
entire algorithmic family. No applicable competitive theorem or implementation
for the proposed decomposition system has been supplied.

The H041 m=5 gate d+s<3/10 applies to B=p^(1/5+o(1)), full-base relation
collection, sparse B² linear algebra and the stated useful-rank assumptions.
It is an exponent condition, not the finite-cost test D<p^(3/10). Finite
admission compares setup + expected attempts + algebra + recovery against the
matched reference. Nor does the B collection factor automatically apply to
a single-useful-relation policy with known affine labels.

Root reread [Amadori–Pintore–Sala, sections 3–3.2](https://pure.tue.nl/ws/files/91158650/609.pdf).
Their points carry known coefficients in P,Q, not generally known logarithms
to P. A useful dependency can recover the unknown log without a full relation
matrix. They leave the polynomial-solving cost unresolved and do not establish
an improvement over rho. For this policy, charge base construction and each
rebuild, expected solving attempts, extraction and verification; no extra B
factor is justified merely by importing the full-collection policy. Tuple
counts are not automatically useful-success probabilities.

## C and short screens: retain identities, withdraw universal claims

For E/Fp, p odd, a finite point over Fp² with rational abscissa has Frobenius
pi(P)=P or −P. On a specified odd-order subgroup, P_±=(P±pi(P))/2 are valid
projections. The minus component belongs to the anti-Frobenius group associated
with the twist; it is not automatically a twist q-part. If both target
components are nonzero, a decomposition into such rational-abscissa points
needs both types, leaving at most m−1 terms in either component. This is a
necessary component identity, not a product-success law. The auxiliary target,
subgroup restrictions and joint distribution need explicit construction and cost.
If the target abscissa is rational too, the literal coordinate equation adds
no second independent coefficient equation by restriction of scalars.

Two line involutions composing to a translation only describes that named
construction. Restricting tuple families does not by itself quantify useful
coverage. Correspondence sums need a defined induced homomorphism and proved
Hom hypotheses; the raw universal Hom=0 claim is withdrawn. Likewise the
statement that only F4/F5 remains unpriced is unsupported and withdrawn.

[Bi–Cheng–Rojas's primary abstract](https://arxiv.org/abs/1204.1113) concerns
univariate sparse root detection, with degree and term-count hypotheses. It
does not alone justify the raw nine-term specialization or its ECDLP reduction.
The quoted algorithmic upper estimate cannot exclude faster structured solvers.
Root's PDF rereads timed out; the accessible abstract was checked, not a fresh
full theorem audit. This screen is unestablished, not a negative result.

## Process, reviews and next decision

Root retrieved the original terminal task through task_status; no new T3 round
or child-thread continuation. Native /root/h007_additive_relations (Astra)
independently checked the resultant, direct-degree scope and Frobenius split.
Native /root/h034_c4_implementation (Sol) independently checked the modular
invoice, output/memory costs and distinction between collection policies.
Both were read-only: no solver runs, imports, edits or children. Root alone
read the primary sources and integrated corrections. Raw claims remain visible.

Source access: web open of the three linked primary sources, find of
Cafure–Matera's field condition and APS's no-improvement passage. BCR PDF
open timed out; abstract open succeeded. Earlier ePrint403 and truncated
institutional-link400 errors remain raw access failures, not model failures.
No seeds or runtime measurements exist for this paper-only wave.

Validation command: ./scripts/check.sh > /tmp/ecdlp-h043-structured-check.log 2>&1.
Result is recorded in STATE after execution; existing Lean checks do not
certify the new paper arguments. Audit.lean is unchanged because no Lean claim
was added. Next conclusion-changing evidence is an explicit faster labelled
reporting/decomposition operator or a separately complete competitive solver,
followed by skeptical review before any newly admitted synthetic falsifier.
