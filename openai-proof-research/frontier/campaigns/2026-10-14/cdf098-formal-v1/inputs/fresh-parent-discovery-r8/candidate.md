# CDF098: connected finite-length nonembedding obstruction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Full proof candidate for original-scope.md SHA256 bb115b9c504b9e5d8e3f62d841bc16095049f23719a47eb13d18d253ed1741c5. No independent proof/contribution PASS or acceptance is asserted. Ambient distances, never graph path distances, are used below.

## 1. Finite polygonal thickening with a uniform ambient doubling bound

**Lemma.** Let X be a finite subset of a real Hilbert space with at least two points, diameter1 and doubling constant at most the integer D>=1. In H⊕R there is a connected finite union G of line segments containing X×{0}, with a distinguished vertex o, radius at most sqrt(2) about o, finite total edge length L, and doubling constant at most Delta=256 D^10. Constants do not depend on |X|, its minimum separation, or dim span(X).

Choose x0 in X and put N0={x0}, s_k=2^(-k). For k=1,...,m choose a maximal subset N_k of X whose distinct points have distances strictly greater than s_k. Maximality makes it an s_k-net. Choose m>=1 with s_m smaller than the minimum separation in X; then N_m=X. N0 is a1-net because diam X=1. For x in N_k choose a parent p_k(x) in N_(k-1) with ||x-p_k(x)||<=2s_k.

Put a vertex (x,s_k) above each x in N_k, join it by a straight segment to (p_k(x),2s_k), and also include the vertical segments {(x,t):0<=t<=s_m} for x in X. Let G be their union and o=(x0,1). This is connected: every vertex has a finite parent chain to o, and every bottom endpoint has its vertical edge. It contains X×{0}. Every projected point is a convex combination of two points of X, so its distance from x0 is at most1. Heights lie in[0,1], so its distance from o is at most sqrt(2). Its total edge length is bounded by

    L = sqrt(5) sum_(k=1)^m s_k |N_k| + s_m |X| < infinity.

Overlaps or intersections among segments only reduce Hausdorff length; neither is assumed absent.

We prove the doubling bound for any ball B_G((p,h),r), including centers inside edges. We may cover different portions separately with centers anywhere in G. A portion lying on one segment has diameter at most2r and is itself an interval, by convexity of a Hilbert ball. Eight balls of radius r/2 with centers on that portion suffice (in fact fewer do). The generous count also avoids endpoint conventions. All other grouping estimates below give diameters strictly below r/2, so an arbitrary member of each nonempty group is an admissible center.

Recall a packing consequence of D-doubling: a set of points separated by more than s in an X-ball of radius R has at most D^q members whenever 2R/2^q<=s. Cover the ball q times and use that each covering ball has diameter at most s.

**Bottom vertical edges.** In this portion the projection lies in X∩B_H(p,r). If nonempty choose one x* there; this intersection lies in B_X(x*,2r). Four halvings cover it by D^4 X-balls of radius r/8. Divide the height interval [h-r,h+r]∩[0,s_m] into at most16 pieces of length at most r/8. Points with projection in one covering ball and height in one piece have squared separation at most (r/4)^2+(r/8)^2=5r²/64<r²/4. Thus this entire portion needs at most16 D^4 half-radius balls, regardless of h or s_m.

Call the remaining segments regular edges. A regular edge of scale s=s_k has height interval[s,2s], its lower projected endpoint x lies in N_k, and every point of the edge is within2s horizontally of x.

**Low center: h<=2r.** A regular edge meeting the ball has s<=h+r<=3r. Split the meeting edges into fine s<=r/64 and intermediate r/64<s<=3r.

For a point q on a fine edge with lower endpoint x, its distance to (x,0) is at most sqrt((2s)^2+(2s)^2)=sqrt(8)s<r/16. (Using the actual edge parameter would improve this constant; it is unnecessary.) Hence ||x-p||<17r/16<2r. If such endpoints exist, choose one x*. They all lie in B_X(x*,4r), which nine halvings cover by at most D^9 balls of radius r/128. Group the fine points by one such covering ball containing their chosen endpoint. Two members have distance less than2(r/16)+2(r/128)=9r/64<r/2. The fine portion therefore needs at most D^9 half-radius balls.

There are at most eight intermediate dyadic scales, since their ratio is strictly less than192<256. For one scale s, lower endpoints of edges meeting the ball satisfy ||x-p||<=2s+r. Choose one x* among them. All such endpoints lie in B_X(x*,4s+2r), whose radius is strictly less than132s since r<64s. Nine halvings give covering-ball diameter less than264s/512<s. The endpoints are s-separated, so there are at most D^9 edges of this scale. Each edge portion needs at most eight half-radius balls. All intermediate edges therefore need at most64 D^9 balls.

Including the bottom portion, the low-center ball needs at most65 D^9+16 D^4<=81 D^10 balls.

**High center: h>2r.** A meeting regular scale satisfies (h-r)/2<=s<=h+r. The ratio of the endpoints is 2(h+r)/(h-r)<6, so at most four dyadic scales occur. Moreover s>r/2. At one scale, lower endpoints lie within2s+r<4s of p; relative to a chosen endpoint they lie in an X-ball of radius less than8s. Five halvings yield diameter less than16s/32<s. Thus at most D^5 edges occur at that scale, and their portions need at most32 D^5 half-radius balls over all scales. With the bottom portion, the count is at most32 D^5+16 D^4<=48 D^10.

Both counts are below Delta=256 D^10. This proves the lemma. There is no inference that G's path metric is doubling or bi-Lipschitz equivalent to its ambient metric.

## 2. The stipulated source supplies finite witnesses

Let lambda=76800 and let S be the fixed lambda-doubling Hilbert nonembedding set in source thm:main. For every positive integer j the finite-witness argument in the complete proof of cor:banach supplies a finite X_j⊂S with at least two points that admits no embedding into Euclidean R^j with distortion at most j. That argument is a product-compactness consequence of the stipulated theorem and is credited to the source.

Each X_j, with its inherited metric, is lambda²-doubling: cover an S-ball of radius r centered in X_j twice to radius r/4, and for each covering ball meeting X_j choose a point of the intersection. The latter centers cover the relevant X_j-ball with radius r/2 by the triangle inequality. Normalize diam X_j to1, preserving both doubling and distortion obstruction. Apply Lemma1 with D=lambda², obtaining G_j in a finite-dimensional Hilbert span, root o_j and total edge-length bound L_j. All G_j have the same doubling bound Delta=256 lambda^20.

For a given infinite-dimensional real Banach space B, the same finite-dimensional Dvoretzky theorem used by source cor:banach supplies a linear T_j on span(G_j) with

    ||u-v|| <= ||T_j u-T_j v||_B <= 2||u-v||

for all u,v in that span (one can take upper distortion strictly below2). This application is to the whole finite graph span, not just its endpoint set. Write Y_j=T_j(G_j-o_j), so0 belongs to Y_j. Every Y_j is connected, a finite union of segments, contained in B_B(0,2sqrt(2)), and has total edge length at most2L_j.

Its doubling constant is at most Delta^4. Indeed the preimage of a Y_j-ball of radius r lies in a G_j-ball of radius r. Four halvings give Delta^4 balls of radius r/16. In each that meets the preimage choose a point of that intersection; every other point of it maps within distance at most2(2r/16)=r/4<r/2. The chosen image centers give the claimed half-radius cover. This is the source's elementary distortion-transfer argument.

## 3. One spine, summable tours, and uniform doubling

Fix a unit vector v in B. Let a_j=2^(-j) and eta=1/100. Choose positive scales rho_j so small that

    2sqrt(2)rho_j <= eta a_j,       2rho_j L_j <= 2^(-j).

Define C_j=a_j v+rho_j Y_j. Its root a_j v lies on the segment I=[0,v], it lies inside the closed ball B_B(a_j v,eta a_j), it is Delta^4-doubling, and its total edge length ell_j is at most2^(-j). Set

    Gamma=I ∪ union_(j>=1) C_j.

This is compact: each C_j and I is compact, and any sequence from clusters whose indices go to infinity converges to0, since ||z||<=(1+eta)a_j on C_j. Each cluster connects to I at its root, so the set is path connected. More strongly it is a Lipschitz image of a compact interval. Start at v, move down I towards0, and upon first reaching a_j v make a closed tour of the finite abstract edge tree defining C_j, traversing each edge in both directions, then resume along I. The image of this tour covers C_j even when geometric edges cross. Its length is at most2ell_j. The total elapsed arclength is at most1+2 sum ell_j<=3. The only accumulation of tours occurs at0, and their radii tend to zero; defining the terminal value as0 makes the concatenation continuous. On any finite concatenation it is1-Lipschitz in elapsed time; passing to the limit gives the same inequality up to the terminal time. Rescaling the resulting finite interval to[0,1] gives a Lipschitz map with image exactly Gamma. In particular H^1(Gamma)<infinity.

For completeness the spine does not destroy the uniform doubling bound. Fix any Gamma-ball of radius r about any point x in Gamma. The part on I is contained in a segment of length at most2r, and five balls of radius r/2 with centers on I cover it. All clusters with a_j<=r/4, along with0, lie in the single Gamma-ball B_Gamma(0,r/2), because (1+eta)r/4<r/2.

Let J consist of indices of clusters meeting the ball with a_j>r/4. If i<j and p in C_i,q in C_j, then

    ||p-q|| >= (a_i-a_j)-eta(a_i+a_j)
             >= (1/2-3eta/2)a_i = (97/200)a_i.

If at least two clusters occur, the least index i has a_i<=400r/97 since its point and a point in another intersecting cluster are within2r. All scales in J then lie in(r/4,400r/97]; their ratio is less than1600/97<32, so at most five dyadic scales occur. If only one cluster occurs, no bound on its scale is needed. For each j in J choose y_j in the intersection. The cluster portion of the ball lies in B_Cj(y_j,2r), which two applications of Delta^4-doubling cover by Delta^8 balls of radius r/2, with centers in C_j. Thus at most

    6+5 Delta^8 <= Lambda := 10+6 Delta^8

half-radius balls cover the original ball. Lambda is a finite universal integer independent of B and all the finite witnesses.

## 4. Nonembedding of the full curve

Suppose Gamma embeds bi-Lipschitzly into a finite-dimensional real normed space. The zero-dimensional target is impossible because I is nontrivial. For a positive-dimensional target, compose with a linear isomorphism to Euclidean R^k, obtaining some finite distortion A. Choose an integer j>=k with j>=2A. The normalized original X_j sits isometrically in the bottom slice of G_j. Its placement into C_j distorts distances by at most2; translation and rho_j add no distortion. Restrict the proposed embedding to this copy of X_j and include R^k isometrically into R^j. This gives an embedding of X_j into R^j with distortion at most2A<=j, contradicting its choice.

Therefore Gamma satisfies both clauses of the exact frozen CDF098 target in every infinite-dimensional real Banach space.

## Attribution and limitations

The source supplies the nonembedding set, finite witnesses, qualitative Dvoretzky use and separated shrinking-cluster estimates. Summable traversal of finite graphs is elementary. The additional proposed operation is Lemma1's height-separated ambient doubling thickening, including its low/high-center and bottom-edge analysis. It changes neither the ambient metric nor the source finite witnesses. Independent contribution review must decide whether that operation is substantial or already supplied by a primary antecedent. No claim of optimal Lambda, injectivity, Ahlfors regularity, ambient quasiconvexity or explicit witness sizes is made. No computational sampling is used in this proof.
