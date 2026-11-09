# Independent ordinary reconstruction for MathDB 351165 (numerical scope only)

Reviewer personally derived the following, without mathematical code, enumeration, numerical testing, CAS, solvers or formal execution. The author proposal was challenged, not assumed. This proof is not a full-literal qualification: the source equality predicate and standing-domain issue are isolated in GAP.md. All graphs below are finite connected simple undirected unweighted graphs, with at least one cycle, whose blocks are cycles or bridges. Source 2107.00071v2 defines a cactus by pairwise cycle intersection of at most one vertex. In this setting that definition gives exactly these blocks. Source graph conventions and finite n support this intended domain; its text does not explicitly exclude the singleton in its b=0 wording.

Let k>=1, b>=0, cycle lengths s_i>=3, and d>0. Define
 q=3-2 sqrt(2), a=1+q, C=6-4/sqrt(3)-4 sqrt(2/3),
 delta=0 for b=0 and C for b>0,
 N=n+k+b-1=sum_i s_i+2b,
 A=n-q(k-1)-delta, B=N-A=a(k-1)+b+delta.
We prove R>=d A/N. Since d,N>0 this is exactly each requested numerical bound in its respective regime.

## 1. Constants and global accounting

Constructing the block tree from a vertex gives n=1+b+sum_i(s_i-1). For every geodesic, each traversed cycle contributes at most s_i/2 edges and each bridge at most one; therefore d<=N/2. For w_ij=(1/sqrt(i)-1/sqrt(j))^2,
 C=2(w_13+2w_23)>0, 4w_24=q.
We have 0<q<1/4 and 1<a<3/2 by squaring positive rational bounds on sqrt(2) (11/8<sqrt(2)<3/2). Moreover sqrt(2)>4/3 and sqrt(3)<7/4 imply w_13<9/49 and w_23<25/784: indeed 1/sqrt(2)<3/4, 1/sqrt(3)>4/7. Hence C<388/784<1/2<a. Finally 6w_23=5-2sqrt(6)<3-2sqrt(2)=q: sqrt(6)>1+sqrt(2) is equivalent by positive squaring to 3>2sqrt(2).

Since sum s_i>=3k,
 2B-N <= (2a-3)k+2(delta-a)<0.
Thus B<N/2, A>N/2>0. Also B>=0, including k=1,b=0 where B=0. These facts apply to every cyclic intermediate graph, independently of vertex degrees.

For a connected non-singleton graph, summing 1/deg(u) over incident edges yields one per vertex. Expanding squares gives
 sum_edges w_deg(u),deg(v) = n-2R.
The factor of two is essential: source w* in Eq.(1) is w/2.

## 2. Local additions valid even beside leaves

At an attachment vertex of old degree v>=1 put S=sum_neighbors 1/sqrt(deg(w))<=v. Adding one pendant changes R by
 1/sqrt(v+1)-S(1/sqrt(v)-1/sqrt(v+1))
 >= sqrt(v+1)-sqrt(v)>0.
Adding a new s-cycle, identifying only the attachment vertex, changes R by
 (s-2)/2 + sqrt(2)/sqrt(v+2)-S(1/sqrt(v)-1/sqrt(v+2))
 >= (s-2)/2+(v+sqrt(2))/sqrt(v+2)-sqrt(v) > (s-2)/2.
For the strict last inequality, both sides compared are positive, and
 (v+sqrt(2))^2-v(v+2)=(2sqrt(2)-2)v+2>0.
No degree-two-neighbor assumption is used. Source Lemma 2.7(1) has that additional assumption, so citing its conclusion without this reconstruction would not pay mixed leaf attachments.

## 3. Fixed-diameter target changes

For F=A/N, a pendant within b>0 changes (N,A) to (N+2,A+1). Thus
 F_new-F=(2B-N)/(N(N+2))<0.
The first pendant after b=0 changes A by 1-C, so the numerator becomes 2B-(1+C)N<0. R strictly increases in either case.

An s-cycle changes (N,A,B) to (N+s,A+s-a,B+a), delta unchanged. Exactly,
 F_new-F=(sB-aN)/(N(N+s)).
If this is nonpositive, the strict R increase suffices. If positive, use d<=N/2 and B<N/2 to obtain
 d(F_new-F) < (s/2-a)N/(2(N+s))
             <= s/4-a/2 < (s-2)/2 < Delta R.
Here s/2-a>0 since s>=3 and a<3/2. The penultimate inequality is s/4+a/2-1>0, which follows from s>=3,a>1. Consequently every diameter-preserving block addition to an already cyclic graph makes the ratio slack strictly positive. Mere monotonicity of R was not sufficient; F can increase.

## 4. Isometric full-block skeleton and growth

Choose diametral vertices u,v in G. If they lie in the same block, take that full block. Otherwise follow the unique route between their incident positions in the block-cut tree and take every full block on that route. Call the resulting graph H. Distances inside H agree with distances in G: an excursion into an omitted component returns to the same articulation vertex and cannot shorten a path. The same argument applies to every connected union of full blocks containing H. Each such union contains u,v, has diameter at least d, and by isometry has diameter at most d. Its diameter is exactly d.

Root the finite block structure at H. Add an adjacent omitted block before its descendants. It meets the present graph at exactly one vertex; it adds either a pendant edge or a full cycle. This covers all omitted blocks. A vertex that is an articulation in G need not remain one in H; the BC-tree assertion refers to the actual BC-tree of H. That actual BC-tree is a path. This is the same diameter skeleton as source Lemma 3.3/Figures 3 and 5, with explicit intermediate-isometry justification. H need not contain a cycle even when G does.

## 5. Cyclic chain bases

Suppose first H contains k>=1 cycles. A chain has only degrees 1,2,3,4. Every cycle-cycle junction at a vertex is degree 4. Every bridge-cycle junction is degree 3; other vertices on bridge runs have degree 2, except terminal leaves. Cycle edges between two articulation vertices require care: for i,j>=2, putting x=1/sqrt(i),y=1/sqrt(j),z=1/sqrt(2), we have z>=x,y and
 (x-z)^2+(z-y)^2-(x-y)^2=2(z-x)(z-y)>=0.
Replacing a cycle edge joining articulations by two hypothetical degree-two endpoint charges therefore increases the defect bound, never decreases it.

In a bridge-free chain, each of k-1 shared vertices has four incident cycle half-edge charges w_24, for total at most q(k-1). Thus 2R>=n-q(k-1)=A.

For a mixed chain, order the cycles along the chain. A direct cycle-cycle shared vertex costs at most 4w_24=q. A bridge run between consecutive cycles has two degree-three endpoints: the cycle charges total 4w_23. A one-edge run joins degrees 3 and 3 and costs zero on that edge; a longer run costs 2w_23 on its two ends and zero internally. Its total cost is at most 6w_23<q.

There are at most two external bridge arms beyond the first/last cycle. A length-one arm has defect 2w_23+w_13=C/2. An arm of length at least two has defect 3w_23+w_12<C/2, because
 w_13-w_12-w_23=2(1-1/sqrt(2))(1/sqrt(2)-1/sqrt(3))>0.
This accounting partitions every bridge run and every articulation charge; adjacent cycle articulations are already covered by the splitting inequality. Missing arms only improve the estimate. Thus total defect<=q(k-1)+C and again 2R>=A. In both regimes A>0 and d<=N/2 imply R>=A/2>=d A/N.

This directly proves the chain bases, rather than trusting the source's sign-switching prose in Theorem 4.6. In particular its discussion labels contributions to 2R-n while using positive defect terms; the actual defect identity and inequality directions above avoid that ambiguity.

## 6. Tree skeleton and first cycle

If H is acyclic it is a path of length d. Here d>=2: a connected simple diameter-one cactus with a cycle is K3, whose diametral full-block skeleton is that cycle. The d-edge path has R=d/2+sqrt(2)-1. Grow all required bridge blocks up to the first cycle; pendant monotonicity ensures current R is no smaller. If the current tree has b>=d edges and the first cycle has s>=3 edges, then afterward
 N=2b+s, n=b+s, A=b+s-C,
 d A/N=d/2+d(s/2-C)/(2b+s)<=d/2+s/4.
For the last bound, s/2-C>0, 2b+s>=2d and d/(2b+s)<=1/2. The first-cycle increment yields
 R_new>d/2+sqrt(2)-1+(s-2)/2
      =d/2+s/2+sqrt(2)-2>d/2+s/4,
since s>=3 and sqrt(2)>5/4. This is strict, includes d=2,k=1 and odd cycles, and does not assume the tree itself satisfies a cyclic formula. Subsequent additions are covered by Section 3. This completes both numerical inequalities for the full intended k>=1 range.

## 7. Exact numerical equality, independent of the source adjective

The following is a derived characterization of numerical equality, NOT a proposed definition of longitudinal symmetry. Every extra block beyond H makes the bound strict, including the tree-first-cycle case. Equality therefore forces G=H, hence an actual BC-tree path. Since A>0, equality in the chain proof forces d=N/2 as well as maximal defect.

For b=0, equality holds exactly for an even single cycle, or a chain of even cycles whose two articulation vertices on every internal cycle are antipodal. Terminal cycles have just one articulation and supply the free antipodal diametral endpoints. Necessity: a diametral geodesic must use every cycle and exactly half of every cycle, which forces even lengths and antipodal entrance/exit vertices. Sufficiency: concatenate these half-cycle routes, yielding d=N/2; articulations are nonadjacent so the defect bound is attained. No reversal symmetry of the sequence of cycle lengths is needed by this numerical characterization.

For b>0, maximal defect requires both external arms, each of length one, and no bridge run between cycles: a missing arm loses C/2; a long arm loses the strictly positive difference above; an intercycle bridge run costs strictly less than q. Therefore b=2 and both bridges are pendant end arms. Additionally all cycles must be even and their two entrance/exit vertices antipodal (for k=1 these are the two pendant attachment vertices). Conversely these conditions give d=N/2 and exact defect q(k-1)+C, hence equality. They also preclude adjacent articulation vertices on any cycle.

A useful exact challenge is C4 with length-two arms at opposite vertices. Here k=1,b=4,n=8,N=12,d=6, so d=N/2, and its defect is D=2(3w_23+w_12)<C. Thus R/d=(8-D)/12>(8-C)/12. It has two leaves, an actual BC-tree path, and ordinary reflections along and across its axis. Whether it satisfies the source adjective is UNESTABLISHED. This is not claimed as an authenticated refutation of the full literal.

## 8. Decisive complete source-to-numerical-target bridge

After independently reconstructing the proposal, compare the ACTUAL stronger additive statements already printed in the same primary source. Theorem 5.2 (pp17-18) asserts, for b=0,
 R-d/2 >= n/4-(k-1)(7/4-sqrt(2)).
Theorem 5.4 (pp19-20) asserts, for k>0,b>0,
 R-d/2 >= (n-b)/4-(k-1)(7/4-sqrt(2))-C/2.
These are both exactly
 R >= J := d/2+A/2-N/4,
because q/2+1/4=7/4-sqrt(2). For EVERY cyclic cactus in the stated regime, Section 1 proves A/N>1/2 and N/2-d>=0. Now the exact identity
 J-d A/N = (A/N-1/2)(N/2-d) >=0
immediately gives BOTH numerical ratio bounds. This is the complete applicable source-theorem bridge, not a shortness judgment, an abstract, or a generic standard-tool objection. No assumption that a cycle addition decreases F is needed for this bridge. The author's own Section 6 notes that cycle additions can increase F; it overlooks the use of its stronger half-diameter additive bound.

To ensure this exclusion is not hiding the source proof's unaddressed mixed-leaf and tree-skeleton cases, the stronger additive premises can themselves be reconstructed from the independently justified Sections 1,2,4,5,6 above: on a cyclic chain, R>=A/2>=J. A mixed pendant changes J by zero; the first pendant changes it by -C/2. An s-cycle changes J by s/4-a/2, strictly less than Delta R by the same inequality s/4+a/2-1>0. If H is a tree, after the first cycle J-d/2=s/4-C/2, whereas R_new-d/2>s/2+sqrt(2)-2>s/4-C/2. All growth preserves d. Thus all range and degree hypotheses of both old additive statements are paid, including k=1,b=1,d=2 and tree-first-cycle. Source proof slips are repaired by elementary inequalities already displayed, without a new graph invariant or stronger premise.

The equality implications of this numerical corollary are not automatic: the factorization forces d=N/2 (since A/N>1/2) as well as equality in the old additive bound. Section 7 supplies the numerical equality characterization independently. The literal source adjective still must be authenticated. The numerical subset is therefore a direct prior-source corollary, ZERO discovery credit even if independently formalized. This does not falsely label the entire ambiguous equality-bearing MathDB statement as already proved or refuted.
