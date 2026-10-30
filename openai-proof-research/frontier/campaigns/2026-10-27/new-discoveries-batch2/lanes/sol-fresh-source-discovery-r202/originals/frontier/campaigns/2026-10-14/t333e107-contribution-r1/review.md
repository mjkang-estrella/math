# T333E107: independent contribution review, round 1

**Verdict: TECHNICAL, conditional on correctness.** The frozen theorem has a
stronger global conclusion than source333, but its added operations reduce to
the source's already transverse oscillation geometry and elementary tubular
geometry, compactness, differentiation, and finite induction. I find no
substantial unpaid operation at the full frozen target under the campaign's
stated criterion. This is a contribution verdict, not a proof-gate PASS or
FAIL, an acceptance, or a count instruction.

The campaign state supplied for this task is 18/20 (R023–R040), with two
remaining. This review awards zero credit and makes no ledger change. The
parent decides integration and acceptance. This is the first independent
contribution round; no prior independent contribution objection is assumed.

## Exact object and premise boundary

The target is: for every closed smooth orientable surface M, including
disconnected and empty surfaces, and every smooth positive definite metric g,
there exists a smooth isometric embedding M -> R4. There is no restriction on
curvature, genus, analyticity, or size; no prescribed initial-map approximation,
knot class, regular-homotopy class, or uniform estimate. This review evaluates
that whole target. It does not substitute immersion, local realization, C1
regularity, or R5.

The pinned source statements **and proof operations** at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. Their correctness
is not reviewed. The original author proof, scope, comparison, hostile checks,
reading limits, provenance, verifier, control receipt, and manifest were read.
The four detached author digests supplied in the assignment match, including
manifest `e3b992016df3fadbe6fc223e9f1dfb9565f435b9afe9ed81705a495453ffdb6f`.
The retained source files match the Git blobs in the complete 13,223-entry,
nontruncated `sources/preprints-tree.json`. Neither hashes nor the author's
integrity replay establish mathematical correctness or substantiality.

## Why the stronger headline does not earn this gate

Source333 already solves all smooth metric realization and all geometry needed
to run the finite construction. Its `lem:velocity-plane` proves that the
tangential projections of F_y and F_yy are independent, by the strict phase
Hessian. Consequently P = span(F_y,F_yy)^perp is complementary to dF(TM).
Thus the useful direction of the order-one oscillation is not a new geometric
resource constructed by the author. `lem:velocity-loop` supplies smooth
mean-zero w in P, smoothly zero outside the disk. `prop:primitive-realization`,
`eq:realization-asymptotics`, supplies uniform first-derivative asymptotics
for **already exactly corrected smooth maps**, with exterior C2 convergence.
`geometry-preservation.tex` and the global-preparation and assembly proofs
allow arbitrarily smaller scales at each of finitely many steps.

The remaining observation is that a tubular projection along P kills w.
Changing a tubular complement from the orthogonal normal bundle to a given
smooth transverse bundle does not solve another metric equation or impose
another geometric constraint. It is the inverse function theorem applied to
(p,e) -> F(p)+e, followed by compactness. The cutoff extension of a complement
is linear interpolation of bundle graphs. The cancellation estimate is the
chain rule. C1 openness and choosing a smaller scale finitely often complete
the argument. The full reduction is reproduced below and in
`paid-unpaid-comparison.md`; it is not inferred from a paper title.

This recognizes an actual deductive addition: source333 does not state
embedding preservation, and none of the primary theorem statements inspected
states the frozen smooth closed-surface R4 theorem. Being a distinct deduction
does not make that deduction substantial under a rule explicitly excluding
classical machinery attached to paid operations and routine source-companion
consequences. That rule decides this case.

## Reproducible reduction of the added mechanism

Fix one current smooth compact embedding F and one disk from the paid finite
list. All choices and constants in this paragraph are for this fixed step.

1. **Starting map.** An orientable closed surface has an ordinary smooth
   embedding in R3 by its handlebody realization; inverse stereographic
   projection puts it in S3. Source333 `lem:spherical-preparation` permits
   arbitrary C1 closeness to any fixed spherical immersion I, with uniform
   C2 and immersion bounds. Choose its permitted tolerance inside the C1
   embedding neighborhood. The proof of `lem:global-preparation` starts with
   this fixed I and uses the same uniform family; scaling by lambda > 0
   preserves injectivity. No new preparation, decomposition, or PDE is added.
2. **Complement.** By the source convention,
   Gamma^x_yy = -Hess_gamma x(partial_y,partial_y) < 0. For tangent T in P,
   inner products with F_y and
   F_yy = Gamma^x_yy F_x + Gamma^y_yy F_y + B_yy give
   <T,F_y> = <T,F_x> = 0, hence T = 0. This is precisely the independent
   tangential-projection calculation in source `lem:velocity-plane`, in dual
   form. It persists on a collar by compactness and strictness. No new
   transversality condition is obtained or needed.
3. **Global bundle and tube.** Orthogonal projection P -> N_F is an
   isomorphism, so P is a graph A:N_F -> dF(TM) locally. A cutoff chi, one
   near the closed disk, gives the global graph E = graph(chi A); every such
   graph is complementary to the tangent bundle. At (p,0), the differential
   of Phi(p,e)=F(p)+e is (u,v) -> dF_p(u)+v and is invertible. The inverse
   function theorem gives local tube charts. If arbitrarily small uniform
   fiber neighborhoods failed to be injective, colliding pairs would have
   fiber lengths tending to zero. Compactness and injectivity of F give the
   same limiting base point. Both pairs then lie in one inverse-function
   chart, a contradiction. This gives a smooth Q = F composed with the base
   projection, satisfying QF=F, DQ(F)dF=dF, DQ(F)|E=0. Orthogonality is not
   used in this tubular-neighborhood proof. No global frame is required.
4. **C0 control is paid or elementary.** In the actual source proof,
   `eq:finite-ansatz` gives f_z[G] = G + sum(z^j U_j(G;x/z)), with G=G_m -> F
   in C3. The coefficients have O_s(s^(-p1)) bounds under
   `eq:slow-map-bounds`, and `eq:fast-asymptotic-scale` imposes
   sigma(p1+2)<1, s=z^sigma. Hence the finite sum is
   O(z^(1-sigma p1)) -> 0 in C0. `prop:exact-correction` adds o(1) in C2.
   This already gives global C0 convergence for the selected exact family.
   Alternatively, the author's mean-zero primitive W gives
   H_z=f_z-F-zW(p,x/z), dH_z -> 0 uniformly. One exterior anchor and finite
   background diameter give H_z -> 0 in C0. The exterior error is retained.
   Both routes are finite estimates; neither is a new convergence scheme.
5. **Cancellation.** The paid exact contract is
   df_z=dF+w(p,x/z)dx+r_z, with ||r_z||_0 -> 0 globally, w in E, and
   ||df_z||_0 bounded. The bound also follows from the fixed exact metric.
   C0 convergence puts f_z in the tube and gives

       d(Q composed with f_z)-dF
         = [DQ(f_z)-DQ(F)]df_z + DQ(F)r_z -> 0.

   This identity uses DQ(F)(w dx)=0. Uniform continuity of DQ on a smaller
   compact tube supplies the first limit. The zero-order limit follows from
   QF=F. Thus Q composed with f_z -> F in C1. This is elementary calculus
   applied to the paid contract, without modifying the oscillation or exact
   correction.
6. **Injectivity and assembly.** C1-close maps to a compact embedding are
   embeddings: in finitely many small convex coordinate balls a suitable
   fixed linear target projection has uniformly invertible derivative and
   a lower Lipschitz bound; pairs away from the diagonal are separated by
   compactness and C0 closeness. Consequently Q composed with f_z is
   injective, which forces f_z to be injective. The paid exact positive
   metric makes f_z immersive. Take the minimum of this scale threshold
   and the source's geometry-preservation threshold. Repeat the already
   paid finite induction. On the finitely many components, separate final
   compact images by translations. The empty case is immediate.

This lists every added step. The only source-specific identification in the
embedding argument is that the source's oscillation lies in an already paid
transverse complement. There is no remaining unpaid analytic, topological
elimination-of-double-points, or global compatibility operation after the
elementary tube argument. It is not necessary to assume uniform reach across
steps, continuous dependence on z, or support-fixed exact correction.

## Closest primary bodies and what they do not pay

[De Lellis–Inauen–Szekelyhidi (2018)](https://ems.press/content/serial-article-files/38715),
Theorem 1.2, Remark 8.1, and the final proof on printed pp.1143–1144 explicitly
handle embedding preservation. Remark 8.1 uses a finite induction and separates
near and distant pairs; the final proof uses derivative control near the
diagonal and uniform separation away from it. This is direct primary evidence
that embedding preservation is an established subsidiary operation. I do not
apply its vector-valued mean-value representation as a general lemma for the
author's large loops. The reduction above supplies the needed estimate instead.

[Cao–Szekelyhidi, 2306.12879v1](https://arxiv.org/pdf/2306.12879v1),
Proposition 3.3 and its entire Section 3.1 proof, use a normal term of size
O(sqrt(delta)) and a tangential term O(delta); the concluding p.14 paragraph
refers to the preceding paper for embedding preservation. Theorem 1.1 gives
C^(1,theta) compact embeddings in R^(2n), theta<1/3 for surfaces. The small
amplitude and lower regularity matter. I do not claim Proposition 3.3 literally
accepts the author's all-size non-normal loops or pays smooth exactness.

[Le Donne, 1005.1623v2](https://arxiv.org/pdf/1005.1623v2), Section 3,
Theorem 3.1, Lemma 3.5, and the construction and injectivity proof, concern
almost length-preserving smooth approximations, tubular path distances, and a
limiting path-isometric embedding. Lemma 3.5 refers elsewhere for its tube
estimate. It is corroborating context, not the oblique-cancellation lemma or
a smooth isometric R4 theorem. Its unread reference does not pay an operation.

The primary comparisons support the standard-method assessment. They do not
prove a verbatim prior appearance of the present deduction. The reduction to
the inverse function theorem, bundle graphs, the chain rule, and C1 stability
is shown explicitly rather than assigned to an unread primary theorem.

## Objections resolved without changing the target

The hostile two-jet really defeats ordinary orthogonal normal projection: at
the stated phase it sends the new x derivative to -e1. An oblique base
projection sends it to e1. This is not dismissed by C0 closeness. The
difference is mathematically useful but routine once P is already transverse:
the construction of Phi works for every complementary bundle, at every fixed
finite amplitude. New tubular coordinates do not constitute new metric
realization machinery. The finite exact algebra checks in `checks.json`
illustrate this distinction and do not prove the theorem.

The initial orientability is authentic to the frozen target. The r5
`screen.md` instead adjusts finite accuracy and leaves noncompact exhaustion
compatibility unresolved. The r17 `source-reading.md` is a navigation/contract
screen, with no embedding proof. The r92 `screening.md` rejects a prescribed
regular-homotopy extension using the positive-curvature normal-Euler
obstruction. None contains this embedding argument, and none permits a
duplicate verdict based on its title. The TECHNICAL judgement here rests on
the present operation reduction, not on relabeling one of those failed targets.

Source334's Theorem A is a local smooth R3 nonimmersion obstruction. Its
complete `main.tex` was read. It explains a lower-dimensional contrast in
source333; it neither obstructs this R4 conclusion nor supplies global
injectivity. Its lower-level proof files are not premises and were not read.

I have not identified an additional mathematical gap material to this
contribution reduction under the stipulated contracts. That observation is
not a correctness certificate. A separate proof gate remains separate.
Attribution or presentation improvements—especially citing classical
embedding preservation and describing the tube as transverse rather than
orthogonal—would improve a note, but would not create an unpaid substantial
operation or change this verdict. No literature-wide absence or priority
clearance is claimed.

## Integrity and disposition

Only `t333e107-contribution-r1/` was written. All 36 author files are anchored
for unchanged-byte checking. Private third-party evidence is segregated under
`private/`; public review prose is original. No shared ledger, staging,
commit, PR, browser UI, contact, upload, nested agent, manuscript, or
formalization was used. `verify.py` is read-only, requires a detached manifest
digest, checks exact payload membership and external anchors, and authenticates
all 13 pinned blobs against the complete tree. Positive copied-bundle and
negative integrity controls are recorded separately. Integrity success
certifies bytes only.

**Disposition for the parent: TECHNICAL conditional on correctness; no
substantial-contribution PASS; no count and no acceptance entered.**
