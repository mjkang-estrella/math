# Path rearrangement and its exact branching limitation

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Parent-supplied path proof, author-checked here; the first branching anchor configuration was derived in this round, and the parent supplied its optimized constant and k-leaf generalization. These are technical route checks, not a weakened replacement for T332.

## A single rooted path

Represent a weighted edge vector by the step function f on the geometric interval [0,L], using each edge length as its interval length. The weighted edge ell1 metric is exactly the L1 metric of these functions. Positive off-root vertex measures correspond to nonnegative nonincreasing step functions; probabilities correspond additionally to values<=1.

Replace f by f_+=max(f,0), or by min(1,max(f,0)) for probabilities. This is L1-contracting and fixes the relevant flows. Take the decreasing rearrangement f# on [0,L]. For nonnegative f,g, its threshold sets are initial intervals of lengths |{f>s}| and |{g>s}|. Layer cake gives

    ||f#-g#||_1
       = integral_0^infinity ||{f>s}|-|{g>s}|| ds
       <= integral_0^infinity |{f>s} symmetric_difference {g>s}| ds
       = ||f-g||_1.

Average f# on the original consecutive edge intervals. Jensen contracts L1. Since f# is nonincreasing, the averages on consecutive intervals are nonincreasing, regardless of their lengths; a bound0<=f#<=1 is preserved. The composition is therefore a 1-Lipschitz retraction onto path cone flows, or path probability flows respectively. Every original feasible step function is fixed. Zero total length is the trivial one-point case.

## Exact 1-contractive branching extension is impossible

A unit stem followed by k>=2 unit leaves has positive-flow cone

    K_k={(r,z_1,...,z_k): z_j>=0, r>=sum_j z_j}

in ordinary ell1. Let x=(k-1,1,...,1). For each j let a_j have stem coordinate k-1, child j equal0, and all other children1. Let y=(k,1,...,1). Every a_j and y lies in K_k, and every distance from x to these anchors equals1.

Any L-Lipschitz retraction has output q=R(x) at distance<=L from each anchor. Average q over all permutations of its child coordinates. Convexity of K_k and of the norm gives a feasible symmetric point (r,s,...,s), with r>=ks>=0, still within L of all anchors. Thus

    L >= |r-(k-1)|+(k-1)|s-1|+s,
    L >= |r-k|+k|s-1|.

The first right side is at least2r/k. To verify this, for r<=k use s<=r/k<=1 and split r at k-1; for r>=k use (k-1)|s-1|+s>=1 and r-k+2>=2r/k. The second right side is at least2(k-r), since |r-k|>=k-r and k|s-1|>=k(1-s)>=k-r. Consequently

    L >= max(2r/k,2(k-r)) >= 2k/(k+1).

The radius lower bound is sharp for these anchors: r=k^2/(k+1), s=k/(k+1) gives all anchor distances2k/(k+1). In particular k=2 forces L>=4/3, and these examples force any universal cone-retraction constant to be at least2.

This does not rule out uniform constants2 or larger, nor direct cone cotype. The path rearrangement proof cannot simply be declared 1-contracting on branching trees. No claim is made that an actual global retraction with the sharp lower bound exists.
