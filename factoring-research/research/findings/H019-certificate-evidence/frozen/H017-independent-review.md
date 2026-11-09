# H017 — Independent review of the conditional tail-supply bound

Date: 2026-10-08. Reviewed the complete
[H017 report](H017-resultant-tail-supply.md) and
[provenance](H017-tail-provenance.json), including their exact constants.

**Disposition: ACCEPT the conditional counting theorem, the rational
certificate, and the stated growing-degree scaling.** No mathematical defect
requiring revision of these claims was found. The certificate design is ready
for a separately preregistered finite implementation experiment. No diagnostic
has been implemented or run here, and practical completion within 60 seconds
has not been established.

**The all-input and randomized-field supply question remains INCONCLUSIVE.
Verified full factoring complexity improvement: NONE.** This review accepts
a population upper bound under computable geometric conditions. It accepts
neither those conditions uniformly for ordinary-base polynomials nor any lower
population, smoothness, rank, or splitting theorem. These are reviewed informal
proofs, not Lean theorems or novelty claims.

Required project instructions, STATE, H017's hypothesis, W001 Card C/shared
accounting, the full H008 independent review and disposition, H013's full
report and disposition, and the full H014 report and independent review were
read. H014's independent acceptance supersedes the historical review-pending
wording in H017; it supplies an enumeration primitive, not useful supply.
H016 processing and H018's general fixed-r analysis are outside this review.

Only this report and adjacent H017-review-* files were created. No proposer
report, prior evidence, shared code, Lean, STATE, registry, or hypothesis was
edited. No packages, delegation, commits, publication, scheduler, factor
advice, root sample, or parameter sweep was used.

1. **ACCEPT — hypotheses, product identity, and removal of large roots
   (H017 equations (2)–(4)).**

   The finite theorem requires N>1, integer H>=1, a monic square-free integral
   f of actual degree d, and genuine quadratics with 1<=a<=H and |b|,|c|<=H.
   Set h=max(a,|b|,|c|). Choose any F of r roots known to have modulus at least
   2H+2, put J equal to its complement, and require k=d-r>=3. Use a strictly
   positive lower bound kappa<=kappa_J. The polynomial f need not be
   irreducible for this count; a number-field interpretation does require it.

   Write R_i=max(1,|alpha_i|). Monicity gives exactly

       |Res(f,g)| = product_i |g(alpha_i)|
                  = M(f)^2 product_i E_i,    E_i=|g(alpha_i)|/R_i^2.

   For x>=2H+2 the triangle inequality gives

       E_i >= 1-H/x-H/x^2 > 1/2.

   The strict last inequality holds already at x=2H+2: the difference from
   1/2 is (H+2)/(4(H+1)^2)>0. Thus including a root exactly on the modulus
   boundary is mathematically safe. A future verifier may use a stricter
   sufficient disk test and leave unresolved roots in J. F need not be maximal
   or conjugation invariant. Taking an unproved large-root classification would
   invalidate the certificate; retaining an extra root in J does not.

2. **ACCEPT — the three-evaluation lemma and resultant lower bound
   (equations (5)–(6)).**

   On any triple of distinct roots in J, the matrix with rows
   (alpha_i^2,alpha_i,1)/R_i^2 has entries of modulus at most one. Its
   determinant magnitude is

       |alpha_i-alpha_j| |alpha_i-alpha_l| |alpha_j-alpha_l|
       / (R_i^2 R_j^2 R_l^2)
       = Delta_ij Delta_il Delta_jl.

   Each inverse entry is a two-by-two cofactor divided by this determinant.
   Cofactors have modulus at most two, so each inverse row has absolute sum
   at most 6/|det|. The coefficient vector (a,b,c) therefore satisfies

       h <= 6 max(E_i,E_j,E_l)/|det|.

   Since |det|>=6 kappa, three evaluations strictly below kappa h are
   impossible. At most two evaluations are below that threshold, including
   when some others equal it. Ordering the k evaluations and writing their
   minimum as e yields

       product_(i in J) E_i >= e^2 (kappa h)^(k-2).

   Multiplication by the F factors proves (6). This argument uses neither
   independent embedding values nor real-root assumptions. Complex conjugate
   roots cause no defect: distinct complex evaluation rows are invertible,
   and all estimates use complex absolute values. Resultant zero gives e=0
   and is consistent with the inequality.

3. **ACCEPT — the cutoff, H008 uniqueness, and the exact count
   (equations (7)–(11)).**

   Expanding the monic root product bounds every coefficient by its binomial
   coefficient times M(f), hence A<=2^d M(f). Substituting into the defined
   threshold T gives T/M(f)^2<=12^d(d+1)H^d N^(-9/(5d)); the direction is
   correct. Combining it with (6) gives

       e^2 <= [2^r 12^d(d+1) H^d N^(-9/(5d))]
              / (kappa h)^(k-2).

   To force e<=1/(144H^3), it suffices that the denominator be at least
   144^2 H^6 times the bracket. This is exactly the stated Y, including
   20736=144^2 and the exponent d+6 on H. No actual-height h was incorrectly
   substituted for the global cube height H in the uniqueness threshold.

   Since R_i^2<=1+|alpha_i|+|alpha_i|^2, a witness satisfying (9) satisfies
   H008's slab with epsilon=1/(144H^4). For two height-at-most-H quadratics
   at that witness, the reviewed padded integer resultant has modulus at
   most 72/144=1/2<1. It is zero. Genuine primitive irreducible quadratics
   with positive leading coefficient sharing a factor are identical. H008's
   zero-constant and complex-root qualifications are respected.

   Assigning one witness in J to each high-height primitive irreducible gives
   at most k such polynomials. All remaining ones have integral height at most
   h_*-1, whose positive-leading containing cube has exactly
   (h_*-1)(2h_*-1)^2 triples. Thus

       S_pi <= (h_*-1)(2h_*-1)^2 + k

   for every integer h_*>=max(1,Y). This is a discrete upper bound, not a
   continuous-volume inference. It remains valid when h_*>H or h_*=1,
   although the ambient cube may give a better bound. The conjugacy-orbit
   refinement is also valid, even if only one member of a pair lies in J.

   All quantities raised to powers in the cutoff equivalence are positive,
   and k-2>0. Hence powering preserves the inequality. With kappa=x/y>0
   rational, equation (11) is exactly the integer comparison

       (x h_*)^[5d(k-2)] N^9
       >= y^[5d(k-2)] [20736 2^r 12^d(d+1)H^(d+6)]^(5d).

   Equality is safe here: it still gives e<=1/(144H^3), followed by the
   strict resultant gap 1/2<1. This differs from H008's unsafe endpoint
   72 epsilon H^4=1. The ceiling fifth root h_*=ceil(H^(4/5)) is obtainable
   by exact integer powers and gives O(H^(12/5)+d) primitive outputs.

4. **ACCEPT — reducibles, contents, and zero resultants (Section 4).**

   For primitive reducible genuine g=u v, primitive integral linear factors
   can be normalized to positive leading coefficients. Mahler multiplicativity
   and M(g)<=sqrt(3)H give H(u)H(v)<=sqrt(3)H. In a dyadic factor-height
   band U<=H(u)<2U there are O(U^2) choices for u and O((H/U)^2) choices
   for v. There are O(log(2H)) nonempty bands. This proves the stated
   O(H^2 log(2H)) count with an absolute constant, independent of d or f.

   Summing this bound for the primitive part at height H/t over positive
   integer contents t<=H preserves the bound, since sum t^(-2) is bounded.
   Reducibles may provide many distinct linear factors and relation directions;
   the report correctly retains the parity identity R=V+c 1^T, including
   the odd dependency coset. No d-row or d-rank bound follows for this branch.

   For a high-height irreducible-over-Q polynomial g=t g_0, division by its
   positive content decreases every E_i. Its normalized primitive part g_0
   has height at most H and satisfies the same H008 slab at the witness.
   Across all these outputs there are therefore at most k primitive rays,
   and at most H positive multiples on each ray. The low-height cube,
   these kH outputs, and the reducibles prove

       S_all = O((1+Y)^3 + H^2 log(2H) + dH).

   The bound concerns the full genuine-quadratic output, before filters.
   Its O constant is uniform; it is not a newly priced processing algorithm.

   A primitive irreducible quadratic with resultant zero must divide f over
   Q. There are at most floor(d/2) distinct normalized such factors, including
   for nonsquare-free f; each has at most H allowed positive multiples.
   Zero-resultant reducibles are included in the whole-cube reducible bound.
   If f is irreducible of degree greater than two, neither type can have
   zero resultant. Zero norms must not be passed to a nonzero-smoothness or
   field-element argument. The main theorem is not accepted for repeated f
   by silently replacing it with its square-free part and retaining d,T.

5. **ACCEPT — growing-degree limits and exact fractions (equations (13)–(17)).**

   These statements concern sequences N tending to infinity with the specified
   fixed a=153/200, b=189/200, delta=21/10 and D=(log N)^(1/3)(log log N)^(2/3).
   In particular d tends to infinity. If r/d<=rho+o(1) for a fixed rho<1,
   then k-2 is bounded below by a positive constant times d eventually.
   Directly expanding log Y gives

       log Y / D = log(1/kappa)/D
         + [d/(k-2)] [log H/D - 9 log N/(5d^2 D)]
         + 6 log H/[(k-2)D]
         + [log 20736+r log 2+d log 12+log(d+1)]/[(k-2)D].

   The bracket tends to a-q=3497/9800>0, where q=20/49. The last two terms
   tend to zero. Combining the two leading height/threshold terms before
   replacing r/d by its upper bound preserves the inequality direction.
   This proves (13), with degree-dependent constants exposed. It does not
   extrapolate fixed-degree big-O estimates.

   The additive d and dH terms have exponents zero and a respectively; the
   latter is below the reducible exponent 2a. Rounding Y upward changes no
   leading exponent. Thus both exponent bounds in (14) follow. One precise
   interpretation is an upper bound on limsup log(max(1,S))/D; it asserts
   no limit or lower density for the actual population.

   For the actual ordinary-base construction, require m=floor(N^(1/d))>=2,
   actual degree d and leading digit one. Its digits then give A<=m<=N^(1/d).
   Mahler's upper bound M(f)<=sqrt(d+1)A implies

       r/d <= [log N/d + (1/2)log(d+1)]/[d log(2H+2)].

   Since d^2 log H=(a delta^2+o(1))log N, the limsup is at most
   rho_0=1/(a delta^2)=20000/67473. This applies to any certified subset F
   of large roots, without a digit distribution or a real/complex split.

   The exact constants check as follows:

       u_required = 4479883/2381400,
       s_H013 = 18491/9800,
       s_H013-u_required = 1343/238140 > 0.

       beta_0 = 3497/9800,
       3 beta_0 = 10491/9800,
       u_required/3-beta_0 = 193057/714420.

       beta_max = beta_0/(1-rho_0) = 4815369/9494600,
       3 beta_max = 14446107/9494600,
       u_required/3-beta_max = 4066368961/33915660660.

   At lambda=0 the worst allowed removed-root fraction gives primitive
   exponent at most 1.5215076992 and all-output exponent at most 1.53.
   The uniform conditional closing margin is exactly
   lambda<4066368961/33915660660, approximately 0.1198964986.

   For the fixed ceiling-H^(4/5) certificate, the primitive exponent is
   459/250=1.836, and its gap below u_required is 538163/11907000>0.
   Sufficient strict geometry margins are 12503/49000 when rho=0 and
   4976631/47473000 at rho=rho_0. These are approximately 0.2551632653
   and 0.1048307670. The pair-separation implication is correct: multiplying
   three pair bounds and dividing by six costs 3mu+o(1), provided the
   pair-bound o(1) is uniform over all pairs in J as d grows.

   **Endpoint qualification:** the inequalities on lambda are strict.
   Equality at a critical asymptotic value is not settled, because lower-order
   terms and strict population deficits are then uncontrolled. Finite equality
   in (11), by contrast, is accepted. A single finite certificate gives an
   exact finite count; it does not itself prove an asymptotic exponent or a
   finite useful-relation deficit against the heuristic model.

6. **ACCEPT — rational disks and the independent Rouché verifier
   (equation (18) and Section 6).**

   Every proposed disk must have rational real and imaginary center coordinates,
   rational positive radius, and verified containment of exactly one root of
   this same f. All d roots, not only real roots or one from each conjugate
   pair, are required. Disjointness and root counts cannot be inferred from
   approximate plotted locations.

   The stated U_i is an upper bound on max(1,|alpha_i|); the stated L_ij is
   a lower bound on |alpha_i-alpha_j| by the triangle inequality and the
   coordinate maximum norm. Therefore

       (1/6) min_(distinct i,j,l in J)
       L_ij L_il L_jl / (U_i^2 U_j^2 U_l^2)

   is a sound lower bound on kappa_J. The squared U powers are correct:
   each root occurs in exactly two pair denominators. Positivity is required;
   a zero lower distance yields unknown/refinement, not a zero-valued usable
   certificate. At most O(d^3) rational operations suffice for the triple
   minimum after O(d^2) pair computations.

   The disk proof compares the Taylor linear term f'(z_i)(z-z_i) with the
   remainder on |z-z_i|=t_i. The strict inequality (18) makes the former
   dominate, so Rouché gives exactly one root, counting multiplicity, and no
   root on the circle. Exact Taylor coefficients, their coordinate-sum upper
   bounds, and the coordinate-maximum lower bound for |f'(z_i)| suffice.
   A successful test for d disjoint disks accounts for every degree-d root.
   A failed test says nothing about absence of a root.

   To make the proposed verifier unambiguous, its disk predicates can use
   exact squared rational comparisons. Disjoint closed disks satisfy
   |z_i-z_j|^2>(t_i+t_j)^2. For R=2H+2, the sufficient condition
   |z_i|^2>(R+t_i)^2 certifies the entire disk outside R. These are elementary
   implementations of the report's conditions, not new population lemmas.
   Retaining an unresolved boundary disk in J must also be reflected when
   recomputing k and kappa_cert. Geometry for an idealized different J cannot
   be substituted for the actually certified one.

7. **ACCEPT — polynomial bit cost and the conservative precision cap,
   with the report's unknown outcome preserved.**

   The cited Mehlhorn–Sagraloff–Wang Theorem 5 was checked directly. For
   integral degree-d polynomials of coefficient bits tau it gives isolating
   disks with prescribed refinement p in soft-O(d^3+d^2 tau+d p) bit work.
   Exact integer coefficients supply the coefficient access; the exact
   square-free check supplies the distinct-root count here. The theorem is
   a constructive primitive, not a complexity bound for an unspecified
   floating root finder. [Primary theorem](https://arxiv.org/pdf/1301.4870v2).

   The certificate's remaining work is also polynomial in the actual input
   and certificate widths. Rational Taylor evaluation, gcd(f,f'), pair/triple
   comparisons, and integer powering require no factorization oracle.
   If numerator/denominator widths of kappa are B_kappa, the cleared (11)
   comparison has width

       O(n+d^2(B_kappa+log(2h_*)+log(2H)+1)).

   Rational disk data of polynomial width give polynomial B_kappa: each
   candidate triple uses a constant number of rational products, and taking
   a minimum selects a rational rather than multiplying all denominators.
   All powers in Taylor evaluation have degree at most d, so their widths
   grow polynomially as well. Construction, verification, and storage must
   all be charged; O(d^3) rational operations alone is not a bit bound.

   The displayed separation bound is valid. With B=2(A+1) and
   m_pairs=d(d-1)/2, the nonzero integral discriminant gives

       1 <= |disc(f)| <= sep(f)^2 B^[2(m_pairs-1)],

   hence sep(f)>=B^(-(m_pairs-1)). Its logarithm is polynomial in d and
   log A. Fine enough disks give constant-factor lower pair distances and
   upper root moduli; taking the minimum over O(d^3) triples does not multiply
   that constant loss by d. This justifies the report's o(D) loss for a
   fixed certified split with a strict asymptotic margin. It supplies no
   desired small value of log(1/kappa_J)/D for ordinary-base inputs.

   The choice p=100Z^6 is accepted as a polynomial resource cap, with failure
   or unresolved checks returning unknown. It is not accepted as a theorem
   that every input passes (11), every chosen disk representation passes the
   sufficient Taylor test, every boundary can be classified within a chosen
   runtime, or a particular implementation runs in 60 seconds. Isolation
   correctness, sufficient-test success, geometric obstruction, and practical
   runtime are separate properties. The report makes these distinctions;
   they must survive the implementation handoff.

8. **ACCEPT — the optional ordinary-digit Rouché tests (equation (19)).**

   For nonnegative coefficients and rational R>0, strict dominance
   f_k R^k>sum_(j!=k) f_j R^j makes the monomial f_k X^k dominate on the
   whole circle. Exactly k roots lie strictly inside and none on the circle.
   If k=d-2 at R=2H+2, exactly two lie outside. The same k at R_0<R leaves
   no roots in the intervening annulus. This does not require roots to be real.

   There is no irrational or floating comparison: for R=u/v with positive
   integers u,v, multiply by v^d to compare
   f_k u^k v^(d-k) with sum_(j!=k) f_j u^j v^(d-j).
   Equality gives no conclusion. Negative coefficients would require absolute
   values in the dominance test; the accepted version explicitly uses ordinary
   nonnegative digits. The index here is a polynomial coefficient index and
   should be kept distinct from |J| in implementation variable names.

9. **ACCEPT — conditional interpretation and readiness; REJECT any
   strengthening to achieved useful supply or a general factoring result.**

   Under precisely the unchanged selected-tail smoothness and B-scale
   collection model, an upper attempt exponent strictly below u_required
   contradicts that model's supply requirement at this fixed witness. Norm
   upper bounds do not prove the selected-tail smoothness law. A more favorable
   correlated law, stratification by actual height/norm, another field generator,
   or another parameter choice requires separate analysis. Adding losses cannot
   rescue the same model, but H017 does not close every such changed model.

   The report's equation (20) is a valid necessary escape condition along a
   sequence with the stated scaling and k comparable to d. Failure of that
   obstruction is not a population lower bound. Few roots can control the
   minimum triple, and failing the test can coexist with a sparse tail.

   The four quantifiers must remain separate: each fixed input's finite
   implication, a declared random-N distribution, an N-only randomized field
   generator for each fixed N, and explicitly retained exceptional/unknown
   outcomes. No pass frequency, uniform geometry theorem, or field-escape
   probability was proved or estimated here. For independent identically
   costed draws with escape probability theta_N>0, C_sel/theta_N is the
   expected work just to reach a screen survivor; theta_N=0 permits no such
   finite expectation. Useful-relation and splitting success remain additional
   requirements. Repeating the identical deterministic base construction
   does not change f.

   The focused Beresnevich–Bernik–Götze source check is accurate: its Theorem 2
   counts pairs of polynomials of a common fixed degree and height, with
   degree-dependent constants. It supplies neither a fixed-f fiberwise lower
   bound at degrees d and two nor uniform growing-d useful supply.
   [Primary definitions and theorem](https://arxiv.org/html/1501.05767v1).

   **Ready for a separately preregistered finite certificate experiment:
   yes, at the mathematical design level.** Before its one bounded execution,
   the future task must freeze the exact N-only list/seed rule, degree and H
   construction, cutoff, disk generator, independent rational verifier,
   precision and time caps, success criterion, reference and all hashes.
   A pass must mean verified prerequisites, all-root coverage, a positive
   kappa_cert, the exact power inequality, and the resulting finite count.
   Primitive count (10) is explicit; if a numeric all-output bound is also
   requested, its reducible constant must be made explicit rather than
   presenting big-O notation as a certified integer bound. Unknowns, rejected
   prerequisites, errors, timeouts and unstarted cases remain visible.
   No test or implementation is authorized by this review itself beyond the
   separately scoped future task; none was attempted here.

The arithmetic audit was frozen before its single execution under a 60-second
external cap and a 55-second internal budget. It independently reconstructed
the 21 published rational constants and nine comparison/constant checks:
**30 pass, 0 fail, 0 error, 0 timeout, 0 unstarted**, approximately 0.0072 seconds
inside the runner. The largest checked integer had 35 bits, below its registered
512-bit limit. This verifies the displayed fractions and margins, not the
analytic lemmas or any population. The
[protocol](H017-review-arithmetic-protocol.json),
[source](H017-review-arithmetic.py), and
[all outcomes](H017-review-arithmetic-results.json) are retained without rerun.

All 13 H017-proposer input hashes and its report hash matched at this review's
post-read capture. The 16 required input hashes and final documentation hashes
are recorded in [review provenance](H017-review-provenance.json). Hash checks
establish byte correspondence, not historical execution chronology. At the
completion capture, shared research/STATE.md had changed; this reviewer did
not edit it, both hashes are retained, and all other reviewed inputs were
unchanged. No new
geometry, density, enumeration, smoothness, or factoring experiment occurred.
No shared implementation changed, so shared solver/Lean builds were not run.
The cleared integer predicates and bit-width explanations above expand the
existing proof; no new stronger population theorem is silently introduced.

The parent can accept H017's conditional representation/population result as
independently reviewed informal mathematics and retain the stronger-tail
all-input proposal as unresolved. **Verified full factoring improvement
remains NONE.**
