# T333E107: the full frozen embedding target

Author deduction relative to stipulated upstream operations; no independent
proof or contribution verdict. This is an original research note, not a copy of
an upstream or primary paper. The scope is exactly `scope-freeze.md`.

**Claim.** Every closed smooth orientable surface M, with every smooth positive
definite Riemannian metric g, has a smooth isometric embedding into Euclidean
four-space. Disconnected and empty surfaces are included. There are no curvature,
genus, smallness, or analyticity assumptions. No quantitative uniformity,
prescribed-map approximation, or knot-class assertion is made.

All source333 statements and proof operations below are used as stipulated at
revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This note does not audit them.
Exact raw URLs, Git blobs verified against the complete tree, and SHA256 hashes
are in `upstream-provenance.json`.

## 1. Exact source inputs

Write gamma(F)=F*delta_4. The operative source files all belong to
`preprints/Smooth-isometric-immersions-of-closed-surfaces-into-Euclidean-four-space-September-23-2026/build/`.

1. `global-construction.tex`, `lem:spherical-preparation` and the proof of
   `lem:global-preparation`: one may start with any fixed smooth immersion
   I:M->S^3. Its finite-point preparations I_P are arbitrarily C1-close to I,
   uniformly bounded in C2, and uniformly immersive. Choosing the allowed C1
   tolerance smaller does not remove these properties. A scale lambda>0 and a
   finite list (D_j,x_j,y_j,a_j), 1<=j<=K, are then chosen. The prepared initial
   map F^0=lambda I_P has the required normal and boundary invariants, and the
   prescribed intermediate metrics satisfy

       gamma^j = gamma(F^0) + sum_{i<=j} a_i^2 dx_i^2,
       gamma^K = g,
       Hess_{gamma^{j-1}} x_j(partial_yj,partial_yj)>0 on closure(D_j).

   Each coordinate chart contains the closed disk and a collar; a_j is smooth,
   positive on D_j, and smoothly zero outside it.
2. `primitive-statement.tex`, `prop:primitive-addition`, with its proof in
   `geometry-preservation.tex`: a primitive addition can be realized exactly
   while preserving the global preferred normal, nonzero second fundamental
   form, and every required later-boundary invariant. The proof uses the family
   in the next input, and these properties hold for all sufficiently small
   values of its fast scale. We select that family; we do not infer these
   asymptotics for every immersion with the same metric.
3. `velocity-loop.tex`, `lem:velocity-plane`, `lem:velocity-loop`, and
   `primitive-realization.tex`, `prop:primitive-realization`, equation
   `eq:realization-asymptotics`: for fixed current F and one disk D, let

       Y=F_y, C=F_yy, P=span(Y,C)^perp, v=projection_P(F_x).

   There is a smooth 2pi-periodic vector w(p,theta)=V(p,theta)-v(p) in P_p,
   of mean zero in theta, extending smoothly by zero outside D. For all
   sufficiently small z>0 there is a smooth exact immersion f_z with

       gamma(f_z)=gamma(F)+a^2 dx^2,
       (f_z)_x=F_x+w(p,x/z)+o(1), (f_z)_y=F_y+o(1)

   uniformly on the closed disk. On its exterior f_z->F in C2. These are the
   already exactly corrected maps, not merely approximate ansatz maps.
   `prop:exact-correction` is paid source machinery, and its C2-small correction
   is already included in this conclusion.

The added step is to prove that these particular exact maps remain globally
injective when F is an embedding. The headline immersion theorem alone does
not give this fact.

## 2. Two elementary embedding facts

**C1 openness on a compact domain.** If F:M->R^N is a smooth embedding of a
compact manifold, every sufficiently C1-close smooth map is an embedding.
Here is the needed proof. At each point choose a coordinate ball and a linear
map L:R^N->R^n for which D(LF) at its center is invertible. After a fixed
linear change, make this derivative the identity. On a sufficiently small
convex ball the derivative of LF differs from the identity by less than 1/4.
For all sufficiently C1-close G, that of LG differs by less than 1/2. Integrating
along straight line segments proves |LG(u)-LG(v)|>=|u-v|/2 on that ball.
Take finitely many such balls with smaller balls still covering M. A Lebesgue
number ensures that sufficiently close domain points lie in a common larger
ball. Pairs outside this neighborhood of the diagonal have a strictly positive
minimum of |F(p)-F(q)| by compactness and injectivity. C0 closeness excludes
collisions for these pairs. The derivative is injective by the local estimate;
compactness then makes each injective G a homeomorphism onto its image.

**Oblique tubular projection.** Let E be a smooth vector subbundle of
M x R^N such that R^N=dF(T_pM) direct-sum E_p for every p. There is a neighborhood
U of F(M) and a smooth Q:U->R^N such that

       Q(F(p))=F(p),
       DQ(F(p)) dF_p=dF_p, and DQ(F(p))|E_p=0.                 (2.1)

Indeed Phi(p,e)=F(p)+e on E has invertible differential along the zero section.
Compactness gives a uniform small fiber neighborhood on which its differential
is invertible. It is also injective on a sufficiently small such neighborhood:
otherwise distinct pairs (p_k,e_k),(q_k,e'_k) with both fiber norms tending to
zero would have the same image. Subsequence limits satisfy F(p)=F(q), whence
p=q. Both pairs then eventually lie in one inverse-function neighborhood at
(p,0), a contradiction. Thus Phi is a diffeomorphism onto its open image U.
Let pi be its base projection and put Q=F composed with pi. Differentiating
Phi at e=0 proves (2.1). No trivialization of the whole normal bundle is needed.

## 3. The source velocity plane is transverse to the old tangent plane

Fix one primitive step with F an embedding. The source's phase condition says

       Gamma^x_yy = -Hess_{gamma(F)} x(partial_y,partial_y)<0.  (3.1)

The Gauss formula for F gives

       C=Gamma^x_yy F_x+Gamma^y_yy F_y+B_F(partial_y,partial_y).

If T belongs to dF(TM) intersect P, then <T,F_y>=<T,C>=0. Since the last term
in the Gauss formula is normal, (3.1) implies <T,F_x>=0. A tangent vector
orthogonal to both tangent basis vectors is zero. Therefore

       R^4=dF(T_pM) direct-sum P_p on closure(D).             (3.2)

Also Y,C are independent there: their tangential components would otherwise
contradict Gamma^x_yy!=0. By continuity these properties persist on a collar
within the coordinate chart. Thus P is a smooth rank-two complement on an
open neighborhood of the closed disk.

Extend P to a global complement E as follows. The orthogonal normal bundle
N_F is a global complement. The restriction of normal projection P_p->N_F,p
is an isomorphism, so P is the graph of a smooth bundle map A:N_F->dF(TM) on
this neighborhood. Choose a smooth cutoff chi equal to one near closure(D)
and supported inside that neighborhood. Extend chi A by zero outside. The
graph of chi A defines a smooth global complement E, agreeing with P on D.
Apply Section 2 to obtain Q for this E.

## 4. C0 closeness follows from the exact source asymptotics

For completeness this is derived from the stated first derivatives and exterior
convergence, without assuming continuity of f_z in the parameter z.
Let W(p,theta) be the unique mean-zero periodic primitive in theta of w.
It is smooth, and smoothly zero outside D, because these properties hold for w.
The map

       H_z=f_z-F-z W(p,x(p)/z)

on D, extended as f_z-F outside, is globally smooth. Differentiation gives

       d[z W(p,x/z)]=w(p,x/z) dx+z d_p W(p,x/z).

Here d_p holds theta fixed. The compact position-period parameter set bounds
d_p W uniformly. Input 3 consequently gives ||dH_z||_C0->0 on all of M.
For connected M choose a point p_0 outside the coordinate disk. Such a point
exists because otherwise the chart containing its closure would cover M,
making the nonempty compact M diffeomorphic to an open subset of R^2.
Exterior convergence gives
H_z(p_0)->0. Using a fixed background metric of finite diameter and integrating
dH_z along paths yields ||H_z||_C0->0. Since W is bounded, this proves

       ||f_z-F||_C0 -> 0.                                    (4.1)

The maps f_z also have uniformly bounded first derivatives, either from Input 3
or from their one fixed positive definite induced metric. Smooth extension by
zero justifies the global differentiation at the support boundary.

## 5. Preservation of global injectivity for one exact step

For small z, (4.1) places f_z(M) in the fixed tubular neighborhood U. Use a
smaller neighborhood with compact closure in U when estimating DQ. Globally,
the source asymptotics take the form

       df_z=dF+w(p,x/z) dx+r_z,  ||r_z||_C0->0,               (5.1)

where the oscillatory term is extended by zero. Since w is in E, (2.1) kills
this term exactly. Therefore

 d(Q composed with f_z)-dF
   = [DQ(f_z)-DQ(F)] df_z + DQ(F) r_z.                       (5.2)

Uniform continuity of DQ, (4.1), bounded df_z, and r_z->0 show that the right
side tends uniformly to zero. The zero-order difference also tends to zero.
Thus Q composed with f_z converges to F in C1, even though f_z itself need
not converge in C1. By Section 2, Q composed with f_z is an embedding for all
sufficiently small z. Equality f_z(p)=f_z(q) would imply equality after Q and
hence p=q. Each f_z already has a positive definite induced metric and is
therefore immersive. Compactness now proves that f_z is an embedding.

The threshold on z depends on the fixed current F, its tubular neighborhood,
the disk, the coordinate data, and the fixed velocity loop. It need not be
uniform across different surfaces, metrics, or primitive steps. Taking the
minimum with the source's geometry-preservation threshold preserves every
source invariant simultaneously.

## 6. Finite global assembly proves the full target

A connected closed smooth orientable surface admits an ordinary smooth embedding
into R^3: by the classification of compact orientable surfaces it is the
boundary of a ball with finitely many handles, realized as a smooth embedded
handlebody in R^3. Composing with inverse stereographic projection gives a smooth
embedding I:M->S^3. This elementary topological input is separate from an
isometric embedding theorem.

In Input 1 restrict the allowed C1 tolerance of I_P using the openness fact
in Section 2. Then every permitted I_P is an embedding. This restriction keeps
the source's uniform C2 and metric bounds, so all subsequent preparation choices
remain available. The final F^0=lambda I_P is an embedding for every lambda>0.

Use the source's finite list and proceed inductively. At step j, F^{j-1} is a
smooth embedding with induced metric exactly gamma^{j-1} and the inherited
source normal, nonzero second form, and later-boundary invariants. The prescribed
phase condition holds for this same metric. Apply Sections 3–5 and choose the
fast scale sufficiently small for both embedding and all source invariants.
This gives F^j with metric gamma^j. There are K<infinity steps, and each choice
is made for the already fixed smooth map from the preceding step. No limiting
map, common reach bound, subsequence, or uniform higher-derivative estimate is
required. The last map F^K is a smooth embedding with induced metric g.

For a disconnected closed M there are finitely many components. Apply the
connected construction on each. Their images are compact, so translating them
far enough apart makes the union injective. Translations preserve induced
metrics. The empty case is immediate. This proves exactly the frozen claim.

## 7. Contribution boundary

The only added mechanism is Sections 2–5: identify the source velocity plane as
a transverse complement and annihilate its entire oscillatory derivative by
projection along that complement. The source pays for exact smooth metric
realization, all PDE estimates and corrections, and the finite geometric
assembly. C1 stability and tubular projections are elementary classical tools.

Embedding preservation during corrugation already appears explicitly in
De Lellis–Inauen–Szekelyhidi, Remark 8.1 and the proof of Theorem 1.2
([published primary paper](https://ems.press/content/serial-article-files/38715)),
and Cao–Szekelyhidi, Proposition 3.3 and its proof
([arXiv v1](https://arxiv.org/pdf/2306.12879v1)). The former uses a finite-step
separation estimate; the latter refers to that standard embedding argument.
Neither cited theorem itself gives the smooth R4 conclusion for all closed
orientable metrics. This observation does not establish that our adaptation is
substantial or new. See `operation-comparison.md` and `reading-limits.md`.

No independent reviewer has validated this proof or the contribution gate.
No campaign acceptance, worldwide priority, or publication readiness is claimed.
