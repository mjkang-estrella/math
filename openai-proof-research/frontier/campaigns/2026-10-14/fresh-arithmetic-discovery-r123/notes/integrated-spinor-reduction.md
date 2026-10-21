# Integrated reduction: ternary orthogonal finite quotients

PREFREEZE / no nominee. This records a source/classical composition, not a frozen substantial theorem or an independent mathematical grade. The source operative inputs are stipulated true. The following calculation accounts for the apparent central-isogeny difficulty identified in feasibility.md. No further unpaid operation in this calculation has been isolated. No worldwide-priority or project-novelty assertion is made.

## 1. Exact working objects

Let k be any number field and D any quaternion k-algebra, allowing the split algebra. Set

    G = D^*,  S = SL_1(D)(k),  Gamma = D^*/k^*.

By Voight Proposition4.5.10, Gamma is SO(nrd|D^0)(k), where D^0 is the three-dimensional reduced-trace-zero space. The quaternion/ternary correspondence identifies this with the orthogonal group of the associated ternary quadratic form up to similarity. No arithmetic lattice, integral model, finite generation, good reduction, odd residual characteristic, or bounded denominator is imposed. The calculation is about the full rational-point group and all homomorphisms to finite groups. It is not a theorem about a selected finite-S arithmetic subgroup.

Let A be the finite set of nonarchimedean places where D_v=D tensor k_v is division. Let R be the real places where D is ramified. Put

    B = nrd(D^*) = {a in k^*: a is positive at every v in R},
    E = B/(k^*)^2,
    H = product_{v in A} S_v,   S_v = SL_1(D_v).

The equality for B is Hasse-Schilling, with its actual norm construction read in Voight14.7. The local norm maps are surjective at all finite places, including dyadic ones (Voight13.4.9). A and R may be empty.

A hat on a discrete group means its FULL profinite completion using all finite-index normal subgroups. For local groups write explicitly

    L_v = completion of D_v^* for its continuous finite quotients,
    M_v = completion of k_v^* for its continuous finite quotients.

These are not the abstract completions of the local groups. Define L=product L_v and M=product M_v over A. Global localization induces a continuous map Bhat -> M. The completed reduced norms give L -> M. Define the compact fibre product

    P = { (ell,b) in L x Bhat : nrd(ell)=loc(b) in M }.

Finally let

    j : (k^*)hat -> P,
    j(a) = ((scalar localization of a at v)_{v in A}, a^2),
    J = image(j).

The second coordinate is in Bhat, since every scalar square belongs to B. J is a compact closed central subgroup. The calculation below identifies Ghat with P and Gammahat with P/J. These are explicit comparison outputs of the already-paid operations, not nominated new statements.

## 2. What MP and elementary approximation already give

For D division, RSS2002 Theorem6.4 already supplies precisely the MP statement for S over global fields. Its proof, Corollaries6.2/6.3 and the surrounding reduction were actually read. It obtains solvability of the finite quotient, puts a derived-series term in its kernel, and invokes openness of successive derived groups. The number-field pinned source foundations.tex1–263 separately gives the finite-index, power-defect and restriction-to-MP operations, and explicitly includes inner type A among established cases. Its new unresolved-type machinery is unnecessary for quaternion groups. For split D, the classical isotropic case applies.

Every finite-index normal subgroup of S is noncentral: S is Zariski dense in its positive-dimensional connected group, whereas a finite-index subgroup contained in the finite center would make S finite. Thus MP controls every finite quotient of S.

Density of S in H can even be obtained here without a new strong-approximation theorem. On the trace-zero affine k-space D^0 use

    c(x) = (1+x)(1-x)^(-1).

Quaternion conjugation sends x to -x, so nrd(c(x))=1. Its inverse on s+1 invertible is x=(s-1)(s+1)^(-1), of trace zero. At a division completion every s in S_v except -1 belongs to this chart; the omitted point is not open. Weak approximation in the affine three-space simultaneously approximates finitely many chart coordinates. Avoiding the denominator zero locus gives rational points of S. Hence its diagonal image is dense in H. If A is empty the assertion is trivial.

Each S_v is compact and profinite: reduced norm1 forces valuation0, so it is a closed subgroup of the units of the maximal order, with a basis of open normal congruence subgroups. Therefore MP plus density identifies

    Shat = H.

This uses the actual abstract-kernel equality from MP. A mere closure theorem would not suffice. No missing finite-defect equality is being repackaged as a new bridge.

## 3. Local finite quotients retain the entire norm-one group

Fix v in A. Write F=k_v, O the unique maximal order of D_v, P_v its maximal ideal, and pi a uniformizer of F. Voight13.3.11 gives an unramified quadratic field K/F and a presentation D_v=K+K t with t^2=pi. In particular P_v=tO=Ot and P_v^2=pi O. Conjugation by D_v^* preserves valuation and every P_v^m.

For m>=1 put U_m=1+P_v^m. For a positive integer r the subgroup

    V_{m,r} = U_m <pi^r>

is open normal in D_v^*. It has finite index: modulo U_m the unit group is finite, and pi^r kills the valuation subgroup up to a finite cyclic quotient. It satisfies

    V_{m,r} intersection S_v = U_m intersection S_v.

Indeed, if u pi^{r a} has norm1, its norm valuation is 2ra, because u is a unit. Thus a=0. Consequently the finite quotients D_v^*/V_{m,r} induce a full neighborhood basis on S_v. This proves the required extension/cofinality directly. It does not assume that an arbitrary representation of S_v extends to D_v^*.

The reduced norm D_v^* -> F^* is a continuous open surjection with compact kernel S_v. Openness follows, for example, from its surjection on units through the unramified quadratic norm (and its open norm maps on sufficiently small units), or the nonzero reduced-trace differential in characteristic zero. The local continuous quotient topology on F^* is its usual topology. Completing gives an exact sequence

    1 -> S_v -> L_v -> M_v -> 1.

Here is the exactness argument rather than a tacit completion rule. The preceding finite quotients embed compact S_v in L_v with its original topology. The quotient L_v/S_v has the universal property for continuous finite quotients of D_v^*/S_v=F^*: these are exactly the continuous finite quotients of D_v^* killing S_v. Hence it is M_v. Compactness and density give surjectivity. This pays both kernel preservation and the quotient operation at every dyadic place too; no uniform p-adic logarithm is used.

## 4. The global multiplicative group: no new extension theorem

The abstract exact sequence

    1 -> S -> G -> B -> 1

is right exact after full profinite completion. Explicitly, the quotient of Ghat by the closure of S has precisely the finite quotients of B, and is Bhat.

The only potential left-exactness issue is already paid by sections2–3. For each open normal neighborhood W of1 in H choose a product of sufficiently small congruence subgroups inside W. The product of the finite local quotients D_v^*/V_{m,r}, pulled back to G, cuts S inside that neighborhood. Thus the full profinite topology on S is induced from G. It follows that Shat=H embeds as the closure of S in Ghat. We have

    1 -> H -> Ghat -> Bhat -> 1.

Local completion and global reduced norm define a map Ghat -> P. The local exact sequences in section3 give

    1 -> H -> P -> Bhat -> 1:

for each b in Bhat, choose a lift of each loc_v(b) through the surjective map L_v -> M_v. The map between these two exact sequences is the identity on H and on Bhat. It is an isomorphism: its kernel lies in H and is trivial; given p in P lift its Bhat-coordinate to Ghat and correct the remaining discrepancy using H. All groups are compact Hausdorff, so the continuous bijection is a topological isomorphism.

Therefore

    Ghat = P.

This does not assert that finite quotients of G arise solely from local D_v^*. The unrestricted global norm completion Bhat is essential. It also does not assert that a quotient of S extends to G by an arbitrary choice of conjugation action; the congruence subgroups explicitly establish the induced topology before completion.

## 5. Scalar quotient and the single global sign

Finite quotients of Gamma=G/k^* are exactly finite quotients of G killing k^*. The closure of k^* in Ghat=P is J: it is the compact image of its full profinite completion and contains the dense scalar image. Hence

    Gammahat = P/J.

There is no unproved descent of a local section or extension here. This is the universal property of the quotient completion applied to the actual scalar subgroup.

To compute the kernel over the spinor-norm quotient, note first that B has finite index in k^*. Its full profinite topology is induced from k^*, since any subgroup of finite index in B also has finite index in k^*. Thus Bhat embeds in (k^*)hat.

The kernel of squaring on (k^*)hat is exactly the original mu_2(k)={1,-1}. One should not prove this by identifying (k^*)hat with a countable product of Zhat: that identification would be false for full completion in infinite rank. Instead use the classical abstract decomposition k^*=mu(k) x L_0, with L_0 free abelian. It follows from Dirichlet's units theorem and the free group of fractional ideals: the principal ideal subgroup is free, its extension by the units splits, and the free part of the units joins that free subgroup.

The full profinite completion of any free abelian group L_0 is torsion-free. If m x=0 in L_0hat, choose any character phi:L_0 -> Z/n. Choose a basis and lift each basis value to Z/(mn); this defines a character psi lifting phi. Its continuous extension satisfies m psi(x)=0, hence psi(x) is a multiple of n and phi(x)=0. All finite cyclic characters separate points of a profinite abelian group, so x=0. Applied with m=2, only mu(k)[2] remains. This works for countably infinite rank as well as finite rank.

In P, a scalar j(a) lies in H precisely when its norm coordinate a^2 is1. Therefore

    H intersection J = diagonal mu_2(k) in H.

When A is empty this is the trivial image. When A is nonempty it is a single order-two diagonal subgroup; it is not the product of independent local signs.

Since E=B/(k^*)^2, right exactness of completion gives Bhat/closure((k^*)^2)=Ehat. The image of J in Bhat is exactly this closed square subgroup. Thus the paid exact sequence is

    1 -> H / diagonal{+/-1} -> Gammahat -> Ehat -> 1.

If A is empty it reduces to Gammahat=Ehat. If A contains one place the diagonal quotient removes its only local sign. No assertion of a split extension is made or needed.

## 6. Precisely how the naive adjoint fibre product loses information

Let Q_v=D_v^*/k_v^*, a compact group, and let

    theta_v: Q_v -> k_v^*/(k_v^*)^2

be reduced norm modulo squares. Its kernel is S_v/{+/-1}. Define

    P_adj = { (q,e) in (product Q_v) x Ehat:
              theta_v(q_v)=loc_v(e) for every v in A }.

Local square-class groups are finite; localization E->k_v^*/(k_v^*)^2 extends to Ehat. The natural map Gammahat -> P_adj is surjective. Both project onto Ehat, and on their kernels it is the surjection

    H/diagonal{+/-1} -> product(S_v/{+/-1}).

For explicit surjectivity, lift any Ehat-coordinate to Gammahat; the discrepancy between its local adjoint coordinates and the desired ones has trivial theta, so can be corrected by an element of H. Its kernel is central and is

    (product_{v in A}{+/-1}) / diagonal{+/-1}.

Its order is 2^(|A|-1) for nonempty A, and1 for empty A. In particular when |A|>=2, declaring Gammahat=P_adj would lose a genuine finite central subgroup. The same lost subgroup can be seen already in the completion of the rational spinor kernel S/{+/-1}, which is H/diagonal{+/-1} by quotient completion.

This calculation is a diagnostic of a too-early quotient by local scalars. It is neither a counterexample to MP nor a newly isolated nonroutine obstruction: the multiplicative-group fibre product and scalar quotient above resolve it completely.

## 7. All finite characters, not just coordinatewise prime data

E is an elementary abelian2 group of infinite rank in the typical number-field examples. Its full completion must be used. Even for a free F_2-vector space with basis (e_i), the character sending every e_i to1 is a homomorphism on finite-support vectors, hence belongs to the full finite-quotient system. It is not continuous for the product topology coming only from the individual basis coordinates: any neighborhood restricting finitely many coordinates still contains some e_j on which it is1.

Consequently a product of prime-valuation parity coordinates does not suffice to replace Ehat. Likewise the continuous finite quotients of local multiplicative groups and the abstract finite quotients of global multiplicative groups are different inputs. The formula preserves that distinction rather than assuming finite local support for all global characters.

## 8. Higher-dimensional comparison and outcome

For number-field nondegenerate q of dimension>=5, the finite-place u-invariant4 implies all Spin(q) finite local groups are isotropic. MP has A empty. Its conclusion and Zariski density force Spin(q)(k) to be perfect and to have no proper noncentral normal subgroup. The spinor image Omega is consequently perfect. For a normal subgroup N of SO(q)(k), either N contains Omega or N intersection Omega is central. In the latter case [N,Omega] is central; for fixed n, its commutator map on Omega is then a homomorphism to an abelian group, so perfectness makes it trivial. Zariski density of Omega makes N central. Thus the normal-subgroup/finite-quotient passage is already the classical spinor-kernel argument. Schulze-Pillot9.22 identifies the spinor norm image by positivity at definite real places, using weak approximation and the Hasse principle. This is a comparison, not a nomination based on weakening a hypothesis.

The ternary calculation above is the sustained developed direction. It explicitly pays local congruence cofinality, completion exactness, global scalar closure, the dyadic interface, the diagonal sign, and unrestricted global characters. None of these remains a new unpaid finite-quotient bridge. The source's novel outer-A/trialitarian/exceptional operations are not required for the quadratic-form cases studied here. RSS already proves the quaternion MP input, and the remaining steps are universal properties and standard local/global quaternion operations with the explicit compatibility checks above.

No substantial full-scope result was isolated after this integration, so no theorem was frozen and no author-proof nominee is submitted. This is an author-level decision, not an independent TECHNICAL verdict. A further result would require an additional, presently unspecified nonroutine operation; there is no precise new conjecture being promoted merely because its proof is absent. Finite-S CSP, integral lattice normal-subgroup problems, arbitrary characteristic-two forms, broader central-simple-degree formulas and character-rigidity extensions were not developed as substitute targets. All old frozen scopes and incoming dispositions remain unchanged.
