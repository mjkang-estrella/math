# Structural218 — independent round-one contribution review

**Conditional disposition: TECHNICAL, for the entire unchanged frozen statement and the entire submitted AUTHOR-PROOF.md. Correctness remains UNDISCHARGED in this role.** This review assigns no correctness result, acceptance, or count. The parent alone combines the independent reviews. No other review or parent mathematical body was accessed.

The condition applies to every quantifier, auxiliary claim, constant and endpoint assertion in the two authenticated files, not merely to the headline nonselection statement. In particular, this review does not convert a repair, a narrower theorem, or a substitute proof into a favorable assessment of the submitted proof. The construction-comparison argument below requires no change to its mathematical content.

The identities of the reviewed originals are:

- THEOREM.md, 3,717 bytes, SHA256 `179ae89c876e18067a24b6be7a43a6eee3d6b4c697ab8d6e07a27d203feda8fe`.
- AUTHOR-PROOF.md, 13,002 bytes, SHA256 `cbfb43a1bf679f28ad840e418009ff4198428d8ba84bd7f22cbb638d40e1619f`.

Both files were read in their entirety. [REDUCTION.md](REDUCTION.md) gives the complete compatible calculation, including all six conclusions and the strongest Hodge/free-period alternatives. [Private reading and access limits](private/READING-LIMITS.md) distinguish actual reading from authentication, metadata, searches, and unread intermediates.

## Why the full contribution is technical

The central operation is a direct compatible composition of operations already present in Source342's flat-torus example and classical four-dimensional reconstruction. The source example supplies a closed e13 correction with prescribed self-dual coefficient and unchanged wedge square; a zero mean gives an exact correction. The submitted support conditions make the needed trace a simple convex interpolation and reduce the remaining period constraint to one scalar weighted mean. The combination yields exactly the frozen eta, for **every** permitted p,f. No unproved positivity estimate or parametric elliptic inversion remains.

This conclusion is not based on calling the author proof elementary, on a failure of naive projection, or on finding a different theorem with a similar headline. The following calculation is the operative reduction.

Set q0=(p(x1)+p(x3))/2 and D0=p(x1)e12+p(x3)e34. The hypotheses immediately give mean(q0)=1 and q0 f=0. The standard fixed-J0 convex interpolation

    D_s=s U+(1-s)D0,
    q_s=s+(1-s)q0

has class [U], positive diagonal coefficients for s>0, and q_s f=s f. In the source's correction operation replace U by this diagonal form. For any h(x1,x3),

    D_s+2h e13

is closed, its self-dual part is q_s U+h V, and its square is exactly 2A_s(x1)A_s(x3)dV. The square is independent of h, since every wedge involving the added e13 vanishes. The correction preserves the exact class precisely when mean(h)=0; this is an actual period calculation on the coordinate two-torus, not a claim that the mean detects all periods for arbitrary two-forms.

The required self-dual direction forces h=q_s a_s. The scalar centering that enforces its mean zero is

    lambda_s=mean(q_s f)/mean(q_s)=s c,
    a_s=s(f-lambda_s),
    h=q_s a_s=s^2(f-c q_s).

These are exactly the submitted a_s and eta_s. Positivity is exact: the self-dual coefficient is positive and the determinant is A_s(x1)A_s(x3)>0. No estimate uniform over arbitrary p is needed. The support conditions are the only property of f used in choosing q_s; f need not be a product bump or have any prescribed zero-set geometry beyond the frozen hypotheses.

DLZ's stronger Hodge alternative works as well. For sigma=q_s(U+a_sV), its harmonic mean is U, so the closed representative of [U] with this self-dual part is U+2dd*G_Delta(sigma-U). It is unique: a difference would be exact, closed and anti-self-dual, hence harmonic and zero. The displayed eta_s has exactly these properties, so the reconstruction returns eta_s itself. This executes the successful alternative instead of using the failure of one projection as contribution evidence. Exact wedge algebra supplies the positivity that a generic Hodge estimate would leave open near s=0.

The universal obstruction is then a standard dual test against the fixed harmonic U,V. For **any** compatible alpha in [U], alpha^+=q(U+a_sV) implies mean(q)=1 and mean(q a_s)=0; for s>0, mean(qf)=s c. Positivity of the Hermitian eigenvalues bounds |alpha| by2q sqrt(1+a_s^2)<4q. This supplies the full measure compactness and localization package by weak-* compactness and testing, as detailed below and in REDUCTION.md. It blocks every compatible endpoint, rather than one prescribed initial value, but that stronger quantifier follows from the same universal scalar moment identity without another construction.

The geometric phenomenon is a useful negative test of a prescribed-class parametric strengthening. It is not literally the statement of the source's sine example. Nevertheless, the acceptance rule excludes routine compatible compositions; after the above exact reduction there is no indispensable nonroutine operation left in the unchanged scope.

## Actual source and primary operations credited

**Source342, both pinned versions.** All 25 canonical blobs were independently fetched at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, authenticated against the complete stipulated preprint tree, and compared byte-for-byte with the admitted author copies. The full October included TeX proof was read in driver order, including the entire cone section and strict-inclusion example. The differing September introduction was read fully; sections02–07 were reused only after actual equality. Both bibliographies were compared, including the changed companion pointer. The two PDFs were authenticated but not visually read.

The paid source package includes the closed lift B=dd*G+H with RB=Id; exactness preservation of (1-BR) on exact inputs; mass-one positive separation; quadratic mass, L2 correction and angular estimates; density existence and positive-density closedness; arbitrary-class intersection pairing; residual pairing with unrelated positive currents; and prescribed-class separation and the strict cone criterion. No such internal proof operation is treated as new. The October criterion uses V=(H_J^-)perp and C=K_J^t intersect V, closure **in V**, and positivity against **every nonzero** element of that closure, with a itself in C. The unrestricted decomposition is K_J^t=C+H_J^-; its compatible-cone sum corollary has the h^-=b+-1 hypothesis. The September cone-sum formulation is separately recorded, not used to obtain anything by comparison with October, and not audited contrary to the truth stipulation.

The final October example already uses U,V,W, normalization of a self-dual fundamental form, the closed correction2f e13+2k e23, exact mean-zero periods, positivity of the reconstructed invariant form, and harmonic-constant anti-invariant rank computations. Its particular sine coefficients allow smooth fixed-class forms near U; the reduction above explains explicitly how the same operation with diagonal interpolation gives the submitted support and moment properties.

**DLZ, [0812.3680v2](https://arxiv.org/abs/0812.3680v2), §§2.1–2.2.** The entire selected sections, including Lemma2.4 and its proof, were read. The decomposition Lambda_J^+=R F plus Lambda_g^- and Lambda_g^+=R F plus Lambda_J^- is the algebraic interface. Hodge reconstruction corrects a self-dual form to a closed one; closed anti-invariant forms are self-dual harmonic. These are precisely the operations used in the compatible reduction and exact kernel calculation.

**DLZ, [1104.2511v1](https://arxiv.org/abs/1104.2511v1), §§3.3,3.4.3 and5.** The metric-related deformations and rank calculations were read at proof level. On a flat torus the condition is simply orthogonality of a constant harmonic form to the varying self-dual direction. Section5 and Donaldson's local argument allow cohomology to move in a maximal positive plane; they do not provide an exact-class local section through the jumping kernel in this target. These actual hypotheses are not replaced by a generic appeal to continuity.

**Donaldson, [math/0607083v1](https://arxiv.org/abs/math/0607083v1), §2,§3,§5.2,§5.4,§5.5.** The full selected proofs and statements were read. Section2 gauge-fixes by d* and solves d* plus d+ after allowing a harmonic positive-plane term. Section5.2 includes a negative endpoint with no compatible form in any class, which does not meet this target's nonempty fibres. Section5.5 is a stronger negative parametric construction: nonlinear unimodular constraints with negative tangents, asymptotic to the constraint from one tamed J, and a fixed-class nonextension derived from a nontrivial loop of symplectic forms. Its construction embeds a given form into a constraint depending on the magnitude of the form, then extends the constraints over a disc. It is not the linear invariance-plus-positivity fibre of a fixed J_t, and its proposition supplies forms for t<1, without the submitted nonempty compatible endpoint conclusion. These are differences in the actual construction and conclusion, not just in the underlying manifold. Donaldson alone is therefore not presented as a complete reduction of Structural218; the explicit source/classical calculation above supplies that reduction.

**Seidel, [math/0309012v3](https://arxiv.org/abs/math/0309012v3), the cited antecedent.** Independently downloaded; actual introduction, local model and fragility proof, and algebraic Floer/quantum-homology nontriviality argument through the proof of Theorem0.5 were read in the recorded ranges. Squared Dehn twists are smoothly trivial and may be nontrivial in the symplectic mapping class group; period changes can remove the latter obstruction. The rational del Pezzo cases in Example2.10 explain the b+=1 application in Donaldson. This strengthens the negative comparison beyond merely recognizing Donaldson's title. Seidel's later analytic TQFT proof of the exact sequence and some geometric/external intermediates were not read; no stronger priority or exhaustive negative-example claim rests on them. The technical reduction of the submitted construction does not invoke Floer theory.

**Draghici–Zhang, [1111.7287v1](https://arxiv.org/abs/1111.7287v1), §§2–3.** The exact-form/Hodge correction and positivity by adding a sufficiently large compatible form were read. The latter changes the class; it cannot preserve the prescribed scalar harmonic moment here. This is credited as an available operation, with its actual class freedom.

**Li–Zhang, [0708.2520v4](https://arxiv.org/abs/0708.2520v4), entire §3.** Actual structure-current, normalized compact-base, separation, compatible-class and cone comparison arguments were read. They are a classical baseline for the routine positive-measure compactness/duality operations; they are not parametric representative selection results. Statements were read as printed, without auditing the stipulated upstream derivations that cite them.

**Lejmi, [2006 local compatibility theorem](https://www.numdam.org/item/10.1016/j.crma.2006.10.017.pdf).** Theorem1, its local elliptic proof and the two following remarks were read. It concerns local spatial solvability using the projected elliptic operator and jet construction, not a global exact-class parametric lifting. Extraction damage is explicitly retained; the review does not rely on a visually certified reproduction of its symbol formulas.

**Li–Ning, [2607.18778v1](https://arxiv.org/abs/2607.18778v1), §§2.1–2.2.** The actual open-taming/convexity path argument and the integrable compatible-family argument using Kodaira–Spencer and parameter partitions were read. The hypotheses allowing those local compatible sections cannot be omitted. Their proof does not settle the submitted fixed-class lifting problem, and their stated scope is not used to deny the four-dimensional free-class local section furnished by Donaldson/DLZ and the paid lift.

**Pinned compatible-family companion.** The actual smooth-compatible-family subsection of05-families was read, with the original positive-plane and rank-two harmonic-kernel assumptions. Both September and October companion05-families files were independently fetched and shown byte-identical. The proof uses smooth kernel projections, generalized inverses, local corrections and parameter-only convex patching; the class may move. Its global hypersymplectic endpoint development is not part of this review, and no excluded prior hypersymplectic attempt was reopened.

## All frozen assertions covered by the conditional disposition

1. **Every p,f, fixed geometry, flat parameter path and common tamer.** The support identity applies to every admitted pair, not just the example product bump. Quaternionic algebra gives J(a), its fixed orientation and U(v,J(a)v)=|v|^2/sqrt(1+a^2). The bound |a_s|<=5/16 gives the claimed constant1/2. Smooth composition with the standard flat function gives the joint smoothness and every positive parameter derivative at0. Smooth norm bounds are for a fixed input pair on the compact parameter interval.

2. **Exact compatible class and degenerate endpoint.** The reduction reproduces the frozen eta_t exactly. Its zero cross-period and two diagonal means give [U]. Its square is positive for every positive t. At0 it gives the specified smooth semipositive form, zero on {f>0}; U separately belongs to the endpoint compatible fibre. The proof's periodic primitives, rather than a vague appeal to cohomology, were included in the full reading.

3. **Every representative, every delta, all constants.** Pairing with U,V gives the unique positive q, integralq=1 and integralqf=s c for each positive t. Hermitian eigenvalues give |alpha|<=4q. Nonnegativity yields the exact sc/delta bound for every delta>0, including trivially empty superlevel sets. No equation obtained by dividing by s is asserted at0.

4. **Every sequence and every weak limit; the auxiliary limit theorem is retained.** The coefficient total variation is bounded by4. Weak-* subsequences exist on the compact torus. Closedness passes to distributions. The constant coefficient means remain U; the Fourier primitive at each nonzero k proves the distributional class, without an unproved smoothing assertion. Uniform J convergence and the mass bound imply J0-invariance and nonnegativity for every limit. The moment estimate makes every compactly supported test in {f>0} tend to0, so all such limits have the frozen support. A smooth positive compatible endpoint has positive trace against nonzero nonnegative f. Thus it is excluded universally, and distributional continuous selections on any [0,epsilon], epsilon in(0,1], are impossible. C0/smooth selections are consequently excluded. The statement does not require all limits to be singular: the explicit smooth degenerate endpoint is retained.

5. **Exact kernel jump and bounds.** The closed anti-invariant forms are constant self-dual harmonics uU+vV+wW. The equality u+v a_t(x)=0 gives the stated spans at0 and at every t>0, because f is nonconstant. Hence2 becomes1, while b+=3 and g stays fixed flat. A constant-rank inverse argument cannot cross this endpoint.

6. **Full successful free-class family.** The submitted zeta=U+2a e13 is closed, invariant and positive with square2dV, extends through U, and has exactly the stated period drift2s c(1-s)[e13]. The Hodge reconstruction of that same self-dual direction also succeeds with class[U]+s c(1-s)[V], providing the stronger positive-plane-period alternative, with determinant factor at least25/32 on the comparison range0<=s<=1/4. This calculation tests the standard local alternative; it is not a second nominee. Neither success removes the exact-class universal moment obstruction.

The free-class local lift can also be executed abstractly with a fixed B0 and the nearby inverse of U_J^-1 R_J B0 on the fixed anti-invariant bundle; its harmonic component explains the period freedom. Parameter partitions preserve closedness only because the weights depend on the parameter, and preserve invariance only because all summands at a given parameter are invariant for that same J. Fixed-J convexity cannot create a missing exact-class local section. These compatibility conditions are included rather than assumed.

## Adversarial contribution objections and their disposition

**C1 — The source uses sine coefficients, so the support/period construction is unpaid.** Location: COMPARISON.md, “Integrated construction,” and AUTHOR-PROOF.md §§2,4. A possible author response is that choosing the diagonal trace and cross term simultaneously is the real innovation. The response is assessed by the explicit recipe above: fixed-J0 convex interpolation supplies q_s; the single weighted mean uniquely supplies the scalar shift; the source's null-wedge correction supplies exact periods and positivity. The entire recipe works for every frozen input. This contribution objection to TECHNICAL is resolved without altering any submitted formula. The fact that the exact result need not have been stated before is not contested.

**C2 — The universal nonselection and every-limit package is stronger than a failed extension of one chosen form.** Location: THEOREM.md parts3–4; AUTHOR-PROOF.md §§5–6. This distinction is correct and essential. It is fully retained. Once the above construction exists, the universal harmonic moment, positivity bound, measure compactness and fixed smooth tests yield every asserted quantifier and endpoint obstruction. No extra nonroutine operation has been identified there. No submitted statement is narrowed.

**C3 — Donaldson's example has different hypotheses, so it establishes a substantial residual.** Location: COMPARISON.md primary comparison item4. The different nonlinear constraint and endpoint scope are real; they prevent treating Donaldson alone as a duplicate of the target. They do not establish a residual after the separate explicit compatible source/classical reduction. This objection is resolved by that reduction, not by dismissing the hypothesis differences or by inferring priority from unread references.

**C4 — Smooth free-class local solutions or convex patching should eliminate the proposed obstruction.** Location: AUTHOR-PROOF.md §§7–8 and COMPARISON.md local alternatives. Those operations succeed when periods may move, as explicitly calculated. They do not solve the exact-class moment condition near a positive endpoint. The kernel jump explains why the companion's smooth generalized inverse hypothesis is unavailable. This does not change the target; it identifies the precise scope of the successful comparison.

**C5 — Entire proof correctness.** Location: every frozen assertion and every argument in AUTHOR-PROOF.md, including its auxiliary distributional class and positivity arguments. **UNRESOLVED IN THIS ROLE.** I have read and used the whole proof to assess contribution but do not assign a correctness verdict or discharge this condition. Another independent role and the parent must determine whether the entire unchanged submission is correct. Artifact verification has no bearing on this obligation.

**C6 — Exhaustive history and literature priority.** Not established. The guarded search found no eligible overlapping original mathematical section after heading and construction classification. It excludes many useful-looking paths by design, and the primary coverage is bounded. No old scope is reopened, renamed or regraded. Unread material does not establish newness. The conditional technical disposition has a positive full compatible reduction as support and does not require an exhaustive claim that no other antecedent exists.

## Limits and handoff

There is no unresolved construction-comparison bridge in the reduction supporting conditional TECHNICAL. Correctness of the entire unchanged statement and proof remains expressly undischarged. Worldwide priority, exhaustive project-history clearance, full primary intermediate coverage and a formal endpoint proof are not claimed.

The direct original readings and independent downloads were kept local and private. The author selection's bytes and modes were checked by exact manifest paths before and after; the author verifier was authenticated and read, but its directory-walking routine was not run on the author root because the review's admission is path-specific. Root mode0700 was observed separately. The outside author ANCHORS metadata was first observed late and its weaker timing is disclosed. No author file was modified or resealed. No peer review/status, git operation, nested agent, browser UI, contact, upload, publication or downstream work was performed.

Own packet controls and detached anchors concern only artifact identity. They do not change this mathematical disposition or its correctness condition.
