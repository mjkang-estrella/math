# I25 resumed — A rooted entropy budget closes the coefficient-3/2 induction

Date: 2026-10-09. Corpus premise: all supplied proofs at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true.

**Disposition: complete candidate proof, ready for separate independent proof and significance review.** For every finite loopless labelled multigraph with a perfect matching, the requested prescribed-mean coefficient $3/2$ follows from the stronger rooted inequality proved below. The additional bridge is a vertex-star reserve that pays every tight-cut separator exactly. It allows induction to remove nontrivial tight cuts *before* applying the covariance trace, replacing the general supported-face codimension bound by the degree-equation bound. Neither the new proof nor its significance has independent acceptance. No priority claim or accepted-count change is requested.

The original I25 was cancelled before a report/seal; the cause is unestablished. Its partial artifacts and commentary are not premises. The original and resumed task JSON, AGENTS.md, full I22 report, current ledger and complete preprint tree are frozen in [inputs.json](../sources/i25_matching_entropy_improvement_resumed/inputs.json). The original source/experiment trees, including vendor files, were read only: [original-checkpoint.json](../sources/i25_matching_entropy_improvement_resumed/original-checkpoint.json) records all 1,226 files. Only the assigned resumed report/source/experiment paths were written. No agents, index edits, staging, commits, pushes, or other-project edits were made.

## 1. Exact candidate and scope

Let $G=(V,E)$ be any finite undirected loopless multigraph, with parallel edges distinguished by labels, $|V|=2m\ge2$, and at least one perfect matching. Write $P(G)=\operatorname{conv}\{\mathbf1_M:M\text{ perfect}\}$. For **every** $x\in P(G)$, including boundary means, use natural logarithms and $0\log0=0$, and define

\[
 H_G(x)=\max_{\mathbb E\mathbf1_M=x}\operatorname{Ent}(M),\quad
 F_G(x)=-\sum_e x_e\log x_e,\quad
 B_G(x)=-\sum_e(1-x_e)\log(1-x_e),\quad D_G=F_G-H_G.
\]

For a vertex $v$, put

\[
 b_v(x)=-\sum_{e\in\delta(v)}(1-x_e)\log(1-x_e),\qquad
 W_{G,v}(x)=B_G(x)-b_v(x)
           =-\sum_{e\notin\delta(v)}(1-x_e)\log(1-x_e).
\]

**Rooted theorem (candidate).** For every such $G,x$, and **every** $v\in V$,

\[
 \boxed{\quad D_G(x)\le\frac32 W_{G,v}(x).\quad}                 \tag{R}
\]

In particular,

\[
 H_G(x)\ge F_G(x)-\frac32\bigl(B_G(x)-\max_v b_v(x)\bigr)
          \ge F_G(x)-\frac32(1-1/m)B_G(x)
          \ge F_G(x)-\frac32 B_G(x).                         \tag{U}
\]

The middle step uses $\sum_v b_v=2B$, hence $\max_v b_v\ge B/m$. No bound on degree, connectivity, edge multiplicity, or the number of tight cuts is imposed. Empty graphs have $F=B=H=0$ separately; (R) has no root on an empty graph. Graphs without perfect matchings have no feasible mean to which the assertion applies.

This is an entropy-existence theorem. The separator step gives an explicit conditional gluing rule **given** child laws. No polynomial prescribed-mean sampler or numerical optimizer is asserted. The proof of the universal leaf bound uses compactness and a second-variation contradiction.

## 2. Exact source interfaces and comparison with I22

The pinned source is *Entropy and Face Dimension of the Perfect-Matching Polytope*. Selected original bytes are independently checked against their Git blob hashes and the frozen complete tree; [pinned-manifest.json](../sources/i25_matching_entropy_improvement_resumed/pinned-manifest.json) records immutable raw URLs and SHA-256. [source-contracts.json](../sources/i25_matching_entropy_improvement_resumed/source-contracts.json) stores exact statement slices, and [read-passages.json](../sources/i25_matching_entropy_improvement_resumed/read-passages.json) identifies the proof passages used.

The proof uses these strongest interfaces, not merely the introduction:

* `02-polytope.tex`, `geom:thm-polytope`, `geom:lem-face`: degree, nonnegativity and odd-cut constraints describe $P(G)$; its minimal-face tangent space is the kernel of the active constraints. Thus, at a positive mean with no nontrivial tight odd cut, $d\ge s-2m$, where $s=|E|$. This is the **no-tight-cut branch of the source proof**, not a new dimension theorem.
* `geom:lem-gluing`: crossing labels remain distinct in both contractions; choosing the common crossing label and independently sampling the child laws conditionally gives a valid parent law. `geom:lem-reduction` gives the exact zero/value-one coordinate reduction.
* `03-entropy.tex`, `ent:continuity` and `ent:exponential`: $H$ is attained and continuous, and the entropy-maximizing law is a positive finite exponential law on the atoms of the minimal face. Its covariance has range the tangent space.
* `ent:trace`, especially `ent:second-variation`: stationarity cancels the acceleration term along exponential tilts. The source's original unrooted objective yields $0\ge d-s+(c+1)m$. Section 5 derives the rooted version explicitly rather than citing that formula with an altered objective.
* `ent:components`, the full nonlinear Appendix B (`b:thm-nonlinear` and its normalized inverse-covariance proof), the laminar and quotient-space alternatives in Appendix A, the weighted section, and `10-examples.tex` were compared. None of these inspected interfaces states (R) or supplies its reserved star term. Appendix B gives $F-H\le8m(1-e^{-F/m})$; it does not pay the tight-cut separator.

I22 already proved the exact identity $D=D_1+D_2$, but its *unrooted* deficit obeyed

\[
 (F-cB-H)_G=(F-cB-H)_{G_1}+(F-cB-H)_{G_2}+c\,b(q).       \tag{old}
\]

The last term is positive and cannot be dropped. I22's sharp subcubic theorem and scalar ternary inequality are not being relabelled as the contribution. The new step is to reserve one star at **every rooted instance**, with the second child rooted at the contracted vertex. This makes the entire corrected defect additive, as proved next. It is coupled to the no-tight-cut covariance branch to close the induction. A significance reviewer should assess this combination against the source proof, not count its routine corollaries separately.

## 3. Tight-cut gluing and exact separator compensation

Let $S\subsetneq V$ be odd, with both sides of size at least three, $C=\delta(S)$, and $x(C)=1$. Orient the sides so that the designated root $v\in S$. Let $G_1$ retain $S$ and contract $V\setminus S$, and $G_2$ retain $V\setminus S$ and contract $S$ to $z$. Delete edges internal to the contracted side and retain every crossing edge label in each child. Edges becoming parallel remain distinct. Restrict $x$ to obtain feasible $x_1,x_2$; put $q=(x_e:e\in C)$, $h(q)=-\sum q_e\log q_e$, $b(q)=-\sum(1-q_e)\log(1-q_e)$.

Every matching with positive probability under a law of mean $x$ crosses $C$ once: its crossing count is odd and at least one, with expectation one. Such a parent matching is equivalent to two child matchings sharing their crossing label. If $L$ is this label, conditional subadditivity gives

\[
 \operatorname{Ent}(M_1,M_2)\le
 \operatorname{Ent}(M_1)+\operatorname{Ent}(M_2)-h(q).
\]

Conversely, take maximum-entropy child laws at their **fixed** means, draw $L\sim q$, and conditionally draw the children independently given $L$. Labels with $q_e=0$ are ignored. Source gluing produces a law of mean $x$, with equality in the display. Therefore

\[
 H_G=H_{G_1}+H_{G_2}-h(q),\quad
 F_G=F_{G_1}+F_{G_2}-h(q),\quad
 B_G=B_{G_1}+B_{G_2}-b(q).                               \tag{G}
\]

In particular $D_G=D_{G_1}+D_{G_2}$. The star of $v$ is unchanged in $G_1$, while the star of $z$ in $G_2$ is precisely $C$. Consequently

\[
 \boxed{W_{G,v}=W_{G_1,v}+W_{G_2,z}},\qquad
 \boxed{(D-cW)_{G,v}=(D-cW)_{G_1,v}+(D-cW)_{G_2,z}}.       \tag{A}
\]

One can also see the first identity edge by edge: crossing edges not incident to $v$ are charged exactly in $G_1$, and none are charged in $G_2$; every other charged edge occurs in just its retained side. Thus no entropy cancellation or independence assumption conceals the separator payment.

Iterate any finite sequence of nontrivial tight-cut splits, propagating the old root to the side retaining it and rooting the other side at its contracted vertex. The children strictly decrease in order. At every leaf $L$, let $r_L$ be its inherited root. Then

\[
 D_G=\sum_L D_L,\quad W_{G,v}=\sum_L W_{L,r_L},\quad
 \sum_L b_{r_L}=b_v+\sum_{\text{splits }C}b(q_C).             \tag{tree}
\]

The last identity follows by the same root propagation at each split. Applying (R) to the leaves leaves exactly enough reserve to pay **all** terms in (old), while retaining the original root reserve. Conditional gluing up the tree constructs the maximizing parent law from maximizing leaf laws. The matching of crossing marginals is fixed throughout; arbitrary independently chosen means would not suffice.

## 4. Base cases, parallel labels and boundary reductions

### 4.1 A self-contained ternary bound

For $p=(p_1,p_2,p_3)\in\Delta_3$, write $h=-\sum p_i\log p_i$, $b=-\sum(1-p_i)\log(1-p_i)$. We need only

\[
 h(p)\le\tfrac32 b(p).                                  \tag{T}
\]

Here is a complete scalar proof. Put $c=3/2$, $f(u)=-u\log u+c(1-u)\log(1-u)$. It has $f(0)=f(1)=0$, and $f''(u)=-1/u+c/(1-u)$, which changes from negative to positive at $a=1/(1+c)=2/5$. The continuous sum $\sum f(p_i)$ has a maximum. On the boundary it is $(1-c)h(p,1-p)\le0$. At an interior maximum all $f'(p_i)$ agree. Two coordinates above $a$, or one above and one equal to $a$, violate the second-derivative test in their difference direction. Two coordinates equal to $a$ contradict stationarity with the third, smaller coordinate, because $f'$ is strictly decreasing below $a$. If all are at most $a$, stationarity forces $p_i=1/3$, giving $\log3-3\log(3/2)=\log(8/9)<0$.

Otherwise one coordinate is above $a$, the other two are equal below $a$, and they have the form $t,t,1-2t$ with $0<t<1/3$. Set $g(t)=2f(t)+f(1-2t)$. With $u=(1-2t)/t\ge1$,

\[
 g'(t)/2=k(u)=\log u-c\log((u+1)/2),\qquad
 k'(u)=\frac{1-(c-1)u}{u(u+1)}.
\]

The function $k$ starts at zero at $u=1$, increases to a positive maximum, then decreases to minus infinity, with one further zero. As $t$ increases, $u$ decreases; hence $g$ first decreases and then increases. Its maximum is at an endpoint: $g(0)=0$, $g(1/3)=\log(8/9)<0$. This proves (T). I22's same elementary method gives the sharper $c_3=\log3/[2\log(3/2)]$; that sharp refinement is not needed for this proof.

### 4.2 Parallel-edge collapse preserves the entropy deficit

Collapse each parallel class $C_a$ to one edge of a simple graph and let $y_a=\sum_{e\in C_a}x_e\le1$. Write $r^a_e=x_e/y_a$ when $y_a>0$. A labelled matching consists of a collapsed matching and one label in every chosen class. For any law of mean $x$, the chain rule and conditional subadditivity bound its entropy by

\[
 H_{\rm simple}(y)+\sum_a y_a h(r^a).
\]

Indeed each selected-class label has aggregate conditional distribution $r^a$; conditioning additionally on the collapsed matching or other labels cannot increase its conditional entropy. Conversely choose a maximizing collapsed law and, given its matching, choose labels independently with these distributions. This realizes mean $x$ and equality. Also $F_G(x)=F_{\rm simple}(y)+\sum_a y_a h(r^a)$. Thus $D_G(x)=D_{\rm simple}(y)$.

For $\beta(u)=-(1-u)\log(1-u)$, concavity and $\beta(0)=0$ give $\sum_{e\in C_a}\beta(x_e)\ge\beta(y_a)$. Classes are either wholly incident or wholly nonincident to a given root, so $W_{G,v}(x)\ge W_{{\rm simple},v}(y)$. Therefore a rooted inequality for the collapsed graph implies it for the labelled multigraph. Zero classes contribute zero and require no conditional law.

### 4.3 Orders two and four

For two vertices every matching is a single label; $F=H$ and $W_v=0$.

On four vertices first use the preceding collapse. A simple graph has at most the three perfect matchings of $K_4$, which partition its six potential edges into pairs. A law is determined by their probabilities $p_1,p_2,p_3$, with zeroes for absent matching types; feasibility forces both edges of type $i$ to have mean $p_i$. Hence $H=h(p)$, $F=2h(p)$. At any root exactly one of each type's two edges is incident, so $W_v=b(p)$. Formula (T) proves (R), including subgraphs, missing types, and all boundary means. Collapse then gives the base case with any number of parallel labels.

### 4.4 Fixed coordinates in the induction

Deleting edges of mean zero changes none of $F,H,B,b_v,W_v$ and preserves the remaining matching laws at this mean. An edge of mean one belongs to every such law, exhausts the star at both endpoints, and all other incident coordinates are zero. Delete its endpoints and the forced edge, using the source's probability-preserving bijection. If the root survives, all its nonzero incident coordinates survive, so $W_v$ is unchanged. If the root is deleted, its original $b_v=0$, and $W_v=B$. On the residual smaller graph choose any root $w$; its rooted bound implies $D\le c(B-b_w)\le cB$ for $c\ge0$. If the residual graph is empty, $D=B=0$. Thus both root cases reduce to smaller order. Disconnected graphs need no special assumption or independent sampling assertion for this reduction.

## 5. Rooted covariance trace and the complete induction

For fixed root $v$ define $E_{c,v}=F-cW_v-H$. Suppose all retained coordinates satisfy $0<x_e<1$, and $E_{c,v}$ has a local maximum at $x$. Let $T$ be the minimal-face tangent space, $d=\dim T$, $s=|E|$. Take the source's positive maximizing exponential law on that face, with parameter $\theta$, covariance $K$, and tilt curve $y(t)$ for parameter $\theta+ta$. Then $y'(0)=Ka$, $y''(0)\in T$, $\operatorname{im}K=T$, and

\[
 H(y(t))=\log\sum_{M\text{ in face}}e^{(\theta+ta)\cdot\mathbf1_M}
              -(\theta+ta)\cdot y(t).
\]

Set $J=F-cW_v$. Its diagonal Hessian $A$ has

\[
 A_{ee}=-1/x_e+\frac{c\,\mathbf1_{e\notin\delta(v)}}{1-x_e}.
\]

Differentiation, exactly as in the source proof but retaining the indicator, gives

\[
 E'=(\nabla J+\theta)\cdot Ka=0,
\]

and then

\[
 0\ge E''=(Ka)^TA(Ka)+a^TKa+
                   (\nabla J+\theta)\cdot y''(0)
            =(Ka)^TA(Ka)+a^TKa.
\]

The last equality follows since the first-derivative equation for every $a$ makes $\nabla J+\theta\perp T$. Sum along positive eigenvectors of $K$, dividing each inequality by its positive eigenvalue. No commutation of $A,K$ is assumed. Because $K_{ee}=x_e(1-x_e)$, $\sum_e x_e=m$, and $\sum_{e\notin\delta(v)}x_e=m-1$, the necessary condition is

\[
 \boxed{0\ge d+\operatorname{tr}(KA)
             =d-s+m+c(m-1).}                            \tag{RT}
\]

**Induction proving (R).** Fix any $c=3/2+\varepsilon$, $\varepsilon>0$. We prove $D\le cW_v$ simultaneously for every graph, feasible mean and root, by induction on $m$. Section 4 proves $m=1,2$. Suppose $m\ge3$, with the assertion known for every smaller order, and suppose a counterexample exists on a graph $G$ with root $v$. Compactness of $P(G)$ and continuity of $H,F,W_v$ give a **positive global maximum** of $E_{c,v}$, at $x$.

Delete zero edges. The retained point is still a global maximum on the resulting graph: every mean there zero-extends to the original graph with the same objective. If any value-one edge remains, Section 4.4 and induction contradict positivity. Thus all retained coordinates are strictly fractional.

If any nontrivial odd cut is tight at $x$, split it as in Section 3. Both child orders are smaller: if $|S|=2a-1$, then their orders are $2a$ and $2(m-a+1)$, with $2\le a\le m-1$. The two rooted child bounds from induction and exact identity (A) give $E_{c,v}(x)\le0$, again a contradiction. Therefore **no nontrivial odd cut is tight at this positive maximum**.

Only the $2m$ vertex-degree equations now constrain the minimal-face tangent space; coordinates are positive and every other odd-cut inequality is slack. Consequently $d\ge s-2m$. Applying (RT) yields

\[
 0\ge d-s+m+c(m-1)
   \ge(c-1)m-c
   =\frac{m-3}{2}+\varepsilon(m-1)>0.                   \tag{contradiction}
\]

This contradiction proves the induction for every $c>3/2$. For fixed $G,x,v$, $W_v$ is finite and nonnegative. Letting $\varepsilon\downarrow0$ proves (R). This endpoint limit is necessary in this proof: at $m=3,c=3/2$ the lower trace bound is zero, which alone would give no contradiction. The proof nowhere substitutes a local optimizer for a global maximum or assumes that full-polytope entropy is smooth across faces. ∎

This establishes (U), in particular the assigned universal coefficient strictly below two. It does not establish that $3/2$ is optimal. The source's Klee lower bound $c\ge c_3\approx1.354755645675727$ still leaves a gap. A possible further reduction to the six-vertex rooted case is discussed only as an unproved direction in Section 9.

## 6. What the alternative Hessian route does and does not show

The earlier commentary about Klee faces can be reconstructed exactly. In the source family $G_m$, the minimal face at uniform marginals consists of three edge-disjoint matchings $M_1,M_2,M_3$, each of size $m$, partitioning the edges. A law on this face is uniquely $p\in\Delta_3$. At any point of its relative interior,

\[
 H=h(p),\quad F=mh(p),\quad B=mb(p),\quad
 F-\tfrac32 B-H=(m-1)h(p)-\tfrac32m b(p).
\]

At $p=(1/3,1/3,1/3)$, the exact unrooted deficit is

\[
 \boxed{E_{3/2}=m\log(8/9)-\log3<0.}                    \tag{Kval}
\]

For a perturbation $a\in\mathbb R^3$ with $\sum a_i=0$, its second derivative is

\[
 \left(3-\frac{3m}{4}\right)\sum_i a_i^2.               \tag{Khess}
\]

Thus for **every $m>4$** it is a strict local maximum on the whole minimal face. The uniform law has edge covariance $2/9$ on same-colour coordinates and $-1/9$ on different colours. Its two positive eigenvalues are $m/3$, the remaining eigenvalues zero; at this point the unrooted separable Hessian is $-3I/4$. The normalized second-variation eigenvalues are therefore $1-m/4<0$. This verifies the **full** tangent matrix inequality, not just the trace.

All global matching constraints are respected: the three matchings realize the mean, and the source proves that recursive triangle-cut equalities force support onto them. Each vertex star and every tight odd-cut row has zero covariance with the matching vector, since its sum is identically one on all three atoms. Constraints not tight at the uniform point have positive slack. Our exact finite tests verify the colour counts and every tight odd set through twelve vertices; the general facts follow from the face description.

In fact for $m>4$ this is a strict local maximum in the **full** polytope as well. To see the transverse issue explicitly, choose a finite set of exposing tight inequalities whose zero-slack intersection is this face. Summing their nonnegative matching slacks gives zero on the three face atoms and a positive minimum on all other atoms. For any nearby mean $x'$, every realizing law consequently has outside-face mass $r\to0$. Condition on the face: its mean $y\to x$ has its unique three-atom law, entropy $H(y)$. The outside conditional entropy is nonnegative, so

\[
 H(x')\ge h_2(r)+(1-r)H(y).
\]

The smooth function $J=F-3B/2$ is Lipschitz in a neighborhood of the uniform point, where all edge coordinates stay away from 0 and 1; $\|x'-y\|=O(r)$. Therefore

\[
 E_{3/2}(x')\le E_{3/2}(y)+Cr-h_2(r).
\]

For sufficiently small positive $r$, the last two terms have negative sum. If $r=0$, strict maximality on the face applies. This proves the full local assertion (if there are no outside atoms only the face argument is needed). Its value is nevertheless strictly negative by (Kval); matching vertices have deficit zero. Hence it cannot be a positive global counterexample maximum. A strategy that tries to rule out **all** fractional local maxima by strengthening only the star/tight-cut covariance constraints fails on these exact examples. The proof in Section 5 instead uses the positive maximum, the charged separator identity and induction; it makes no such overstrong claim.

For comparison, the rooted quantities on the same family are $D=(m-1)h(p)$, $W_v=(m-1)b(p)$ for every root. Its uniform rooted ratio is exactly $c_3$ for $m>1$, with no denominator floor. These are the source's old extremizers, not a new lower bound.

## 7. Numerical audit and new deterministic diagnostics

The original summaries report 311 graphs / 1,847 Gibbs laws, 140 structured perturbation laws / 49 retained approximately uniform blocks, and 1,032 rooted rows. These are retained **local Float64 diagnostics**, not a global optimization certificate, exhaustive counterexample search, or validated complete computation. Nonfinite output fields and near-boundary numerical instability further limit their use.

The original `search.evaluate` computes $p=\exp(z-\operatorname{logsumexp}z)$, $x=pA$, and $B=-\sum\operatorname{xlogy}(1-x,1-x)$. Float64 rounding can make $\sum p\ne1$ and even $x_e>1$, in which case the negative argument produces a nonfinite $B$. A `B>1e-10` guard does not certify the calculation. `optimize` clips $x$ only in its gradient, so it is not differentiating the original unmodified objective at clipped coordinates; objective and derivative use denominator floors. The rooted optimizer divides by `max(W,1e-12)`. Such a reported quantity is not $(F-H)/W$ whenever that floor is active. None of its convergence flags would prove an extremum even without roundoff.

[original-numerical-audit.json](../sources/i25_matching_entropy_improvement_resumed/original-numerical-audit.json) finds no out-of-range coordinates in the **retained top laws**, but finds 16 nonfinite scalar fields among the rooted summary records. Most non-top laws do not retain their parameters, so neither their means nor a precise cause of each nonfinite result can be reconstructed here. No claim is made that all 1,032 rooted computations have been certified.

The new independent enumerator uses only the Python standard library. It recomputes all 33 retained top laws (15 main, 10 structured, 8 rooted) at **80 and 140 decimal digits**, interpreting each stored JSON parameter as its exact decimal value. This specifies a precise nearby Gibbs law; it does not recover the hidden exact binary value before JSON serialization. It computes absence marginals by summing the probabilities of matchings **omitting** each edge, avoiding subtraction of a near-one marginal. All matching counts agree and ratio differences between the two precisions are below $10^{-50}$. This is a high-precision stability check, not interval certification of these exponential-weight laws.

The suspect rooted record (`n=10,d=3,seed=1,v=1,trial=1` as identified by its retained record) recomputes to approximately

\[
 H=3.45800676549\,10^{-13},\quad
 F=1.72664612304\,10^{-12},\quad
 W_v=1.37848819115\,10^{-12},\quad
 (F-H)/W_v=1.00171002940737091457\ldots .
\]

The original displayed value $1.367744980429948$, with $W_v=9.672204011598472\,10^{-13}$, is discarded as a near-deterministic floor/cancellation artifact. It is **not** an obstruction or a $c_3$ improvement. The other retained rooted maxima are uniform $K_4$ laws, yielding the known $c_3$. The main and structured leaders remain approximately $1.18540860615710073647$ and $1.25051442622842497150$, both below $3/2$. Full recomputations are in [retained-recomputed.json](../experiments/i25_matching_entropy_improvement_resumed/retained-recomputed.json).

The resumed active adversarial screen separately enumerates positive **integer-activity Gibbs laws** on complete graphs, cocktail-party graphs, complete bipartite graphs, parallel $K_4$, a fixed-root boundary example, and Klee chains. Exact enumeration defines rational probabilities and feasible means. Entropy bounds are certified using rational logarithm intervals: reduce $r>0$ to $2^k t$, $1\le t\le2$, write $z=(t-1)/(t+1)\le1/3$, and use

\[
 \log t=2\sum_{j=0}^{N-1}\frac{z^{2j+1}}{2j+1}+R_N,\qquad
 0\le R_N\le\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
\]

The script uses $N=44$ and rounds the rational interval **outward** to a denominator $10^{38}$ before entropy summation. Positive matching weights imply the Gibbs law maximizes entropy at its own means by the finite relative-entropy comparison; arbitrary rational laws would not in general have that property. There are 75 certified laws and 564 rooted checks. Nontrivial cases have a strictly negative rational upper bound on $D-3W_v/2$; deterministic/two-vertex cases use exact identities. The output retains all edges, activities, counts and rational bounds.

Additional exact diagnostics cover nine Klee orders, all tight odd sets through twelve vertices, conditional-product gluing and charged-edge identities on the crossing-one faces of $K_6,K_8,K_{10}$ (9, 45 and 315 atoms), and 291 rational evaluations of the strictly positive trace expression. These computations test the construction and formulas; the universal proof is Sections 3–5, not extrapolation from the tests. See [exact-results.json](../experiments/i25_matching_entropy_improvement_resumed/exact-results.json).

## 8. Current primary comparison and significance limits

Fresh query evidence, current version pages, primary PDFs and extracted text are frozen under [literature/](../sources/i25_matching_entropy_improvement_resumed/literature/), with exact URL/time/hash metadata. The early matching-entropy and later rooted/star/coefficient queries are retained separately. They found no exact duplicate of (R) in the inspected results; search non-detection does not establish worldwide novelty. The complete 749-manuscript inventory and 9,340-text cache were used for a bounded text screen, with retained hit paths and manifest verification. Only selected pinned sources were copied; the corpus and original vendor tree remain read only.

The decisive comparisons are:

* Gurvits, [1106.2844v11](https://arxiv.org/abs/1106.2844v11), Theorem 2.2 and its proof, gives the weighted permanent/Bethe lower inequality. Via entropy duality this supplies $H\ge F-B$ for **bipartite** prescribed matching means, already stronger there. It does not cover the nonbipartite scope of (R).
* Abdi–Cornuéjols–Dadush–Dalirrooyfard, [2505.14497v2](https://arxiv.org/abs/2505.14497v2), Lemmas 6.4–6.5, Corollary 6.6 and Figure 2, supplies laminar rank estimates, exponentially many minimum-cut-respecting matchings for the stated regular degree-at-least-four class, and the three-matching cubic staircase obstruction. The original I25 downloaded v1; this round fetched **current v2, revised 2026-04-20**. Its counting/rank interfaces do not state an arbitrary-prescribed-mean rooted $3/2$ bound. These examples and the source's Klee construction predate this candidate.
* Singh–Vishnoi, [1304.8108v1](https://arxiv.org/abs/1304.8108v1), the introduction's precise oracle interface, Theorems 2.6/2.8 and the finite exponential-family discussion, explains the counting/maximum-entropy connection. Efficient computation requires generalized **weighted** counting/marginal access and relative-interior control; uniform counting by itself is not the claimed oracle. No algorithmic consequence with that missing input is inferred here.
* Dong–Jain, [2609.02017v1](https://arxiv.org/abs/2609.02017v1), Theorem 1.3 and especially Theorem 3.1 with the good-vertex/conditioning proof, improves the **upper** comparison of matching-law entropy to Bethe entropy on bipartite graphs using girth. The relevant direction and graph class differ from this nonbipartite prescribed-mean lower bound. Their local complementary-entropy functional does not supply the charged tight-cut induction used here.
* Dong–Jain, [2609.11049v1](https://arxiv.org/abs/2609.11049v1), Theorem 1.1, gives a deterministic $(1+\varepsilon)^n$ approximation of a nonnegative matrix permanent. It concerns weighted bipartite counts; it is not an all-graph prescribed-mean entropy estimate. The pinned general-graph FPRAS companion states an unweighted simple-input theorem, with weighted intermediate spaces in its proof; those spaces are not silently promoted here to a uniform weighted prescribed-mean oracle.

The intended mathematical difference from the strongest pinned proof is narrow and explicit: change the induction invariant from $D\le cB$ to $D\le c(B-b_v)$; exact root propagation pays separators; a positive maximum then lies in a face constrained only by stars; the modified trace excludes it at every order above the four-vertex base. The covariance facts, maximum-entropy representation, scalar base, and gluing operation themselves are inherited or elementary. Whether this combined invariant and uniform coefficient improvement passes the project's substantial-contribution standard remains for a separate significance reviewer. All counting consequences below are part of this one proposed result.

## 9. Consequences, remaining limits, and review targets

Since $\beta(u)\le u$, the rooted theorem gives $D\le3(m-1)/2$. The source's unchanged Gibbs variational identity therefore yields, for every finite real edge parameter $\theta$, with $Z_\theta=\sum_M e^{\theta\cdot\mathbf1_M}$,

\[
 Q_\theta-\tfrac32(m-1)\le\log Z_\theta\le Q_\theta,
 \qquad Q_\theta=\max_{x\in P(G)}[F(x)+\theta\cdot x].
\]

This is an analytic bracket; no unproved optimization complexity claim is added. If $G$ contains $k\ge2$ edge-disjoint perfect matchings, their uniform mixture has $F=m\log k$, $W_v=(m-1)(k-1)\log(k/(k-1))$. Thus

\[
 N(G)\ge k^m(1-1/k)^{\frac32(m-1)(k-1)}
          \ge k^m e^{-\frac32(m-1)}.
\]

The same substitution applies to a $k$-regular graph with every odd cut of size at least $k$, because the uniform mean is feasible. These consequences improve the source's exponent $2(m-1)$ by the same single bridge; they are not additional proposed findings. Componentwise application after fixed-coordinate deletion gives the analogous sum of rooted bounds on fractional components.

The optimal universal coefficient remains between $c_3$ and $3/2$ under the candidate theorem. At $c=c_3$, the no-cut trace is already strictly contradictory for $m\ge4$, since $3c_3-4>0$. A complete rooted $c_3$ inequality on six vertices would therefore suffice, together with the same invariant and base cases, to prove that stronger bound. This six-vertex statement is **not proved here**; the old rooted search is not its certificate. No optimality assertion or new lower-bound obstruction is made.

Independent proof review should focus on exact labelled-edge entropy gluing, the root bookkeeping in (A), the deleted-root boundary case, the four-vertex multigraph base, the indicator in (RT), and the strict $c>3/2$ induction followed by its endpoint limit. The Klee calculation rules out an overstrong local-maxima argument but does not conflict with this proof.

## 10. Reproduction and artifact integrity

From the project root:

```sh
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i25_matching_entropy_improvement_resumed/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i25_matching_entropy_improvement_resumed/verify.py
```

All diagnostics use Python's standard library; the Python/runtime versions are recorded in [environment.json](../sources/i25_matching_entropy_improvement_resumed/environment.json). No originals are imported, no dependencies are installed or copied from vendor, and bytecode writes are disabled. `literature.py` is the optional network retrieval script; ordinary verification is offline and does not refetch versions.

The verifier checks the report/source/script/diagnostic artifact seal; original file bytes and file inventory, including vendor; frozen input hashes; all selected pinned Git blob/SHA-256 identities against the complete tree; source and primary passage slices; and retained primary bytes. Live shared-input/index drift is reported separately from frozen-artifact failures. The artifact seal excludes only itself and the mutable verification output, avoiding a circular hash. The final audit verifies 70 sealed artifacts, 18 pinned sources, 62 source contracts, 10 source proof passages, 7 primary passages, 20 primary artifacts, all 9,340 cached texts, and all 1,226 unchanged original files. Concurrent live ledger and Git-index drift is reported separately; neither was written by this task. Re-running deterministic diagnostics must reproduce their sealed bytes. See [verification.json](../sources/i25_matching_entropy_improvement_resumed/verification.json).

**Handoff:** a complete source-relative candidate for the universal $3/2$ target, with a stronger rooted statement and explicit separator compensation; numerical artifacts corrected and scoped; no independent review acceptance or count change. Original I25 bytes are preserved.
