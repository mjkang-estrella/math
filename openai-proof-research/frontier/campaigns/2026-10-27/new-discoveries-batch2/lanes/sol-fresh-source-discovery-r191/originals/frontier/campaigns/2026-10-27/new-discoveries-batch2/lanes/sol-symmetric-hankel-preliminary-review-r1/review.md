# Preliminary independent review — recommendation EXCLUDE

29 October 2026. Root owns the decision. This review recommends exclusion from discovery investment under the routine-corollary rule. The ordinary witness is mathematically valid for the displayed analytic class, but its entire increment is the equality realization of the boundary point already isolated in the 2026 source. Full published-source/version comparison remains HOLD. No public prior refutation, formal PASS, acceptance, paper, or additional outcome is claimed.

The 44 files in root's freeze.json matched before review. I copied all 44 bytes-for-byte into frozen-copy, including the complete candidate, caches and provenance. before44hashes.json and after44hashes.json record the original hashes; copy44hashes.json binds my copy. All work was solo and all writes were in this review lane. No git operations, external messages, uploads, accounts, browser tabs or access-control workarounds.

## Source scope and access

The indexed primary material supports Conjecture 1's analytic class, polynomial phi and determinant; the 2026 repetition gives the plus sign on a3*a5. Its defining quotient is over the open unit disk, normalized at zero. The 2026 upper estimate and the boundary optimization are publicly present, but an upper estimate alone is not a refutation. Its conclusion still supports the conjecture. [2026 primary article](https://www.mdpi.com/2073-8994/18/8/1307), [author-upload indexed body](https://www.researchgate.net/publication/411145199_Sharp_Bound_of_the_Third-Order_Hankel_Determinant_for_a_Symmetric_Domain).

Indexed original passages distinguish analytic A from univalent S and use Schwarz subordination. [2025 primary article](https://www.mdpi.com/2073-8994/17/8/1244). The determinant matrix, independently expanded below, controls the sign, rather than a potentially malformed scalar line. The witness also satisfies the classical univalent strengthening, so this distinction supplies no ordinary mathematical escape.

I did not retry either blocked publisher article or the blocked author-upload routes, or fetch alternate publisher paths/hosts. Searches by exact title/DOI plus correction/erratum/refutation, and for independent repositories, found no correction or independently hosted full target manuscript in this bounded screen. No full published PDFs were acquired. Indexed passages are not complete VoR/version/correction comparison: that gate remains HOLD. Search dates are 2026-10-29; search1–5.json preserve returned passages and URLs. Search1 included malformed/overbroad queries and irrelevant hits; those are not clearance evidence. The remaining searches were title-targeted. Source abstract/title rhetoric is not used as a proof.

## Independent ordinary analytic audit

Write D={|z|<1}, u=1/4, w=z²(u+z)/(1+uz), p=phi(w), E=(p(z)+p(-z))/2. The Möbius denominator cannot vanish since |uz|<1. The exact squared-norm difference is (1-u²)(1-|z|²)>0; thus |w|<1 everywhere in D and w(0)=0. Boundary modulus one is allowed.

E is even, holomorphic and E(0)=1, so E-1 has order at least two. Thus q=(E-1)/z extends holomorphically at zero with q(0)=0 and is odd. Every holomorphic function on the simply connected disk has a primitive; equivalently integrate its convergent Taylor series on each compact subdisk. The normalized primitive G exists on all D. Since derivative of G(-z)-G(z) is -q(-z)-q(z)=0, connectedness and normalization give G(-z)=G(z).

Set h=z exp(G), and take the normalized disk primitive f of p exp(G). Then f(0)=0, f'(0)=1, h is odd and h'=E exp(G). The derivative of F=(f(z)-f(-z))/2 is (f'(z)+f'(-z))/2=E exp(G)=h', so F=h by zero value at the origin. The exponential never vanishes, and h has exactly one zero in D, a simple zero at zero. Hence f(z)-f(-z)=2h(z) is nonzero off zero. Cancellation gives the literal quotient p on D minus zero and its removable value 1 at zero. There is no off-disk premise, assumed jet realization, or residual primitive premise in this ordinary argument.

For the optional univalence bridge, on |z|=1 with x=Re z, 9 Re(phi)=6+12x+6x²-4x³. For x>=0 it is >=6. For x=-y, 0<=y<=1, it is 6(1-y)²+4y³>=1/2 (split at y=1/2). Harmonic minimum gives Re(phi)>=1/18, so Re(p)>0 and Re(E)>0 on D. The classical starlikeness criterion applies to h because zh'/h=E and h is normalized with no further zeros. The classical close-to-convex criterion applies to f with this starlike h because Re(zf'/h)=Re(p)>0. Therefore f is univalent on D. These are ordinary classical theorems, not supplied Lean lemmas or extra assumptions on f. The analytic-class proof does not require them.

## Jets and literal determinant

My checker was newly written without reading or running candidate check.py. It builds Taylor coefficients from the rational w and integrates the exponential expansion, then reconstructs them separately through the coefficient recurrence from zf'=p*odd(f). The output is

    (a1,a2,a3,a4,a5)=(1,0,1/8,15/64,-35/768).

Expansion of the literal matrix gives 2a2a3a4-a3³-a4²+a3a5-a2²a5. Its value is -769/12288; the modulus exceeds 1/16 by exactly 1/12288. Both recurrence and primitive calculations agree. independent-check.py, run-check.sh and independent-check.json supply the exact evidence. The first run exposed a checker-only structural SymPy equality issue (factored versus expanded equal expressions); replacing that comparison by exact simplification fixed it. No candidate mathematics was changed.

The checker has hard 512 MiB address-space limits, 20 CPU seconds, 25-second internal alarm, 30-second outer timeout, and BLAS/OpenMP thread counts one. It verifies symbolic identities, not a numerical sample. No claim that finite arithmetic alone proves holomorphic realization is made.

## Decisive substantive bridge: the already isolated equality case

Here P=(1+w)/(1-w) denotes the source's Carathéodory auxiliary function, not my p=phi(w). At l1=0, the published determinant polynomial in Section 2 reduces to

    331776 H = -6048 l2³ + 10368 l2*l4 - 5184 l3².

The source Lemma 1, (5)–(8), gives l2=2alpha, l3=2(1-|alpha|²)beta and

    l4=2alpha²-2(1-|alpha|²)*conj(alpha)*beta²
       +2(1-|alpha|²)(1-|beta|²)rho.

Its edge d12(u)=-20736u⁴+6912u³+20736 is maximized at u=1/4, with value 20763. These are actual indexed formulas, not title inference (search3.json, search5.json).

Here is my independently verified reduction, including phases. Let u=|alpha| and v=|beta|. Substitution in that polynomial gives

    H = -alpha³/48 -(1-u⁴)beta²/16
        +alpha(1-u²)(1-v²)rho/8.

Choose alpha=u=1/4 real and beta=1. The rho term vanishes identically. The two surviving terms have the same negative real phase:

    -1/3072 -255/4096 = -769/12288.

The resulting modulus is exactly d12(1/4)/331776. The ungrouped l-polynomial has cancellation; equality is not being asserted in the triangle inequality applied separately to every raw monomial. The correct test is the source's grouped Schur expression. On l=0,v=1 it is the two terms above; grouping is algebraically exact, all omitted l-dependent terms vanish, and their phases align. independent-check.py checks the published l1=0 polynomial against the reconstructed Schur expression as an identity.

The realization bridge is elementary and explicit. Starting with terminal Schur function beta=1, inverse Schur transform gives S(z)=(alpha+z)/(1+conj(alpha)z). Prepending two zero Schur coefficients gives w(z)=z²S(z). For alpha=1/4 this is exactly the candidate. Direct Möbius algebra proves it is Schwarz, P has positive real part, and its coefficients are (l1,l2,l3,l4)=(0,1/2,15/8,-11/32). They satisfy the displayed parametrization. The disk primitive argument above supplies the normalized symmetric-point f for this P. No novel realization theorem or optimization remains.

The strongest countercase to exclusion is that the source did not notice equality: it still calls 1/16 conjectural, and the candidate supplies a real function where merely maximizing a majorant is insufficient in general. That is a valid logical distinction. It does not defeat the campaign's routine-corollary rule here: the published formulas identify the exact parameter, the standard inverse Schur map realizes it, and the only potential obstruction (phase incompatibility) vanishes by the displayed two-term check. The full analytic bridge is standard disk primitive/odd-part calculus. Accordingly:

- Public prior resolution: NOT demonstrated; an upper bound and optimistic conclusion do not establish it.
- Routine specialization/omitted equality case: demonstrated for the indexed source formulas by the explicit bridge above. Recommend EXCLUDE on this ground.
- Substantive new result: not supported by any mechanism beyond that bridge. Shortness alone was not the reason.

This remains a preliminary root-adjudicated recommendation with full-source HOLD. Even if a full source later contains no explicit refutation, that absence alone would not remove the routine-specialization exclusion.

## Current bounded prior and closest bodies

registry-evidence.json records an independent path screen of the exact scoped frozen caches and live metadata at 10:44:46–48 UTC. The five live heads are unchanged: Omega dev f9745e6af0bfa02fc8c61013f48003ce3e4f9606; main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM 8729eab98bafe409b66c5e39253bf56569a62327; Count dbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Omega's live root confirms the same D5 and Problems tree IDs. Their complete inventories have 12497 and 1544 entries. Main has 69; OpenAI preprints 13578; AIM 3541; Count 183. Whole dev has 55832 entries and truncated=true and is not repository clearance. Chronology metadata: main July 11, OpenAI October 26, AIM October 22, Count September 9; Omega dev's tree response supplies no commit timestamp. A path screen cannot exclude a semantically matching body under an unrelated title.

The name/topic hits in complete Omega scopes concern sequences, combinatorics and Hankel operators; no path identifies this symmetric-point phi functional. OpenAI's two hits are hyperbolicity-cone and similarity-theorem sections, not this object. AIM/Count had no matching paths. These are bounded negative observations, not full-text or worldwide novelty clearance. All live HTTP responses were 200; no rate-limit retry. registry-check.py has hard 512 MiB AS/20 CPU/55 alarm/60 outer-wall bounds and was run with one-thread BLAS/OpenMP settings. The previously saved current registry audit was not used as a substitute for these live comparisons.

I read the cached actual Sun–Kuang body, especially definitions (1.2)–(1.3), Lemma 1.1, Theorem 2.3 and equality examples. Its third initial-coefficient determinant theorem is for the convex symmetric class with a differentiated quotient; the starlike results involve logarithmic coefficients. Thus it does not prove this target. Its Schur/Carathéodory parametrization and implicit-ODE equality examples illustrate the classical machinery used here. [Author preprint](https://doi.org/10.21203/rs.3.rs-4116541/v1).

I also read cached AIMS 11(2026)16811–16836, Definition 1.1, Lemma 3.4, Theorem 4.5/proof and its nonattainment caveat. At lambda=1 its quotient specializes to the relevant one, subject to its K notation. Its bound multiplies separate coefficient estimates through a triangle inequality, and it explicitly lacks a simultaneous extremizer. It does not provide this witness or resolve the exact conjecture in the read section. [Publisher source](https://doi.org/10.3934/math.2026690). Neither source supplies grounds for claiming public prior resolution. Their bibliographies/citing networks were not exhaustively audited.

## Formal disposition

No Lean investment or formal PASS. Since substantive eligibility fails in this review, a fresh library feasibility project is unwarranted. The candidate's plan is an inventory, not a certificate: its future endpoint would have to construct actual disk primitives, establish analytic derivatives and odd-part identity, connect Taylor coefficients to that same f, prove nonvanishing and the quotient, and negate the literal universal determinant claim. If literal source comparison requires univalence, the starlike and close-to-convex criteria must also be proved/imported rather than left as hypotheses. Neither a rational determinant helper nor an assumed realizable jet closes that endpoint. No available-library theorem names or feasibility guarantee were verified here.

Recommendation: EXCLUDE from discovery investment for the explicit routine equality-case bridge; retain full-source/latest-version HOLD and bounded-prior limits. Preserve the valid ordinary construction as uncredited evidence if root wishes. One prospective family only; no sharpness, parameter variants or helpers advanced separately.
