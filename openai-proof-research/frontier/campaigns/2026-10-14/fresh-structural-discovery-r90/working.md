# T328A90 proof attempt

Full target unresolved; no nominee.

## Paid range and exact gap
Source328 proves FPP for every given norm on a reflexive space, and its commuting-family corollary is already paid by Bruck. Wisnicki1203.6635v1 Theorems2.3–2.4 prove asymptotic FPP (even intermediate sense) from SUPER FPP, by passing to an ultrapower and applying the commuting theorem to all variable-iterate maps. Source328 supplies super FPP when X is superreflexive, because every finitely representable space is then reflexive. This range is a routine composition, not the target's new mechanism. For merely reflexive X its ultrapower need not be reflexive; neither its weak compactness nor FPP is licensed by the source.

## Power resolvents and their actual constants
For a power S=T^m with Lip(S)≤k_m and parameter a in (0,1), if (1−a)k_m<1, the map u↦a x+(1−a)S u is a contraction on C. Its unique fixed point R_{m,a}(x) satisfies

Lip(R_{m,a})≤ a/[1−(1−a)k_m],
||S R_{m,a}(x)−R_{m,a}(x)||≤a diam(C),
||R_{m,a}(x)−x||≤(1−a)||Sx−x||/[1−(1−a)k_m].

These follow by subtracting the defining equations and the triangle inequality, without any source theorem. Taking k_m−1=o(a) and a→0 makes the Lipschitz constants tend to1 and gives uniform approximate fixed points of T^m. It gives no uniform approximate fixed points of T. A period-m orbit illustrates why a small m-step defect alone does not control one-step defect. No fixed finite exponent m need have k_m=1.

Source anchor uses exact nonexpansive resolvents with uniform *one-step* defect and displacement controlled by ||Tx−x||. Its convex-composition closure, adaptive selection, and terminal sequence all use these interfaces. Substituting the above power resolvents changes both: the maps are only nearly nonexpansive, and the controlled defect concerns a changing power. A summable Lipschitz error budget might handle finite compositions, but does not itself restore the one-step defect or the diametral lemma.

## Reflexive sequence-space embedding attempt
For selected powers m_j with k_{m_j}−1 summable, consider a shift on sequences with coordinates T^{m_j}. An l^p(X) sum is reflexive for 1<p<infinity. However a backward shift S(x)_j=T^{m_j}x_{j+1} in the weighted p-norm requires w_j k_{m_j}^p≤w_{j+1}; these nondecreasing weights cannot be summable on an infinite tail. Summable weights are needed for the full product of a nontrivial bounded C to lie in this sequence space. Reversing the shift permits decreasing weights but requires an arbitrary first-coordinate boundary condition; a resulting fixed sequence expresses a recurrence and supplies no T-fixed point. Thus this particular reflexive realization does not substitute for Wisnicki's ultrapower. This is not an obstruction to all reflexive realizations.

## Weak limit attempt
A pointwise weak cluster map of T^n is nonexpansive by k_n→1 and weak lower semicontinuity. Source328 gives that map a fixed point. But T need not be weakly continuous, so T cannot be passed through the weak limit, and the fixed point need not satisfy Tx=x. Convexifying maps permits simultaneous norm approximation (source anchor lemma), but destroys exact commutation with nonlinear T. One needs a new way to preserve the orbit/defect information through that convexification.

## Consecutive-power and near-commutation attempt
Normalize diam(C)=D and fix a in C. Put delta_m=k_m−1 and A_m(x)=k_m^{-1}T^m(x)+(1−k_m^{-1})a. Every A_m is an exact nonexpansive selfmap of C, and sup_x||A_mx−T^mx||≤e_m:=D(1−1/k_m)→0. Source328 therefore supplies Fix(A_m) nonempty for each m. Moreover

||A_m A_n x−A_n A_m x||≤2e_m+2e_n.

To verify the bound, insert A_m T^n x, T^m T^n x, A_n T^m x: the four differences are bounded respectively by e_n,e_m,e_n,e_m, using nonexpansiveness of A_m,A_n and exact commutation of T's powers. Thus the tail consists of nearly commuting exact nonexpansive maps.

If a point x satisfies both ||T^m x−x||≤epsilon and ||T^{m+1}x−x||≤epsilon, then
||Tx−x||≤||Tx−T^{m+1}x||+||T^{m+1}x−x||≤(k_1+1)epsilon.
Consequently approximate common fixed points of A_m and A_{m+1}, with errors tending to zero, would give an approximate fixed point sequence for T. This is a real sufficient interface, not yet a proof of a fixed point. Demiclosedness at zero is not available for arbitrary given reflexive norms.

Source's commuting-family corollary requires exact commutation. It supplies neither a uniform modulus for almost commuting maps nor a bounded number of iterates/convex combinations approximating its retraction. A retraction constructed by a limit of arbitrarily long words may accumulate a fixed positive commutator error. Replacing exact commutation by e_m+e_n→0 in that corollary without a new stability argument is invalid. Passing to an ultrapower would make the commutators vanish, but returns to the nonreflexive-ultrapower gap.

Also, pointwise weak cluster maps alone cannot identify a T-fixed point: for T=−Id on a symmetric ball, the even-power cluster is Id, whose fixed-point set is the entire ball, while Fix(T)={0}. This elementary example does not refute the full conjecture or a construction using the entire family of cluster maps. It isolates the need to preserve simultaneous orbit information.

## Orbit metric and its exact convexity obstruction
One can always set d_T(x,y)=sup_{n≥0}||T^n x−T^n y||. This is a metric equivalent to the original one, since the k_n are bounded, and T is nonexpansive for d_T. But d_T need not come from a Banach norm on the given linear structure, and C need not be a convex metric domain in the sense required by the source.

Explicitly take C=[0,1] in the real line and T(x)=max(0,1/2−4|x−7/8|). The range lies in [0,1/2], where T vanishes, so T²=0. It meets the full asymptotic hypothesis with k1=4 and k_n=1 for n≥2, and has the fixed point0. Nevertheless d_T(x,y)=max(|x−y|,|Tx−Ty|). For c=3/4, a=3/4, b=1 and midpoint z=7/8, one has d_T(c,z)=1/2, whereas (d_T(c,a)+d_T(c,b))/2=1/8. Thus distance from c is not convex along the original segment. Also equal original increments1/8 have d_T(0,1/8)=1/8 and d_T(3/4,7/8)=1/2, disproving translation invariance. Therefore applying source328 to this equivalent orbit metric is invalid. The example blocks that transfer, not the fixed-point target.

## Additional source-switching boundary
Source04-switching.tex1–200 actually read. The finite witness proof chooses one terminal b_j whose displacement under every previously fixed tree map tends to zero, while compact detector functionals see nearly diametral differences. It then transports weighted errors through a nonlinear tree and telescopes whole leaf blocks. The new almost-commuting A_m family has not supplied those terminal and detector properties. Even a one-step approximate fixed point sequence for T would not make every changing-power resolvent asymptotically fix its members without a suitable rate/order of selection. The source tree is not asserted to accept the new family unchanged.

## Why averaging does not preserve the useful commutator
A possible attempt is to replace A by its averaged map D_A=(Id+A)/2 to obtain approximate A-fixed points, then invoke source FPP for D_A^N B. This does not propagate the available A,B commutator control: even if AB=BA exactly, B D_A x = B((x+Ax)/2) need not equal (Bx+ABx)/2 = D_A Bx. The difference is a nonlinear Jensen defect, not bounded by ||AB−BA||. The same issue affects convex combinations of powers and resolvents with varying anchor. No affine behavior of the asymptotic iterates has been proved in the given reflexive norm. This prevents silently using an averaging-based commutator accumulation estimate.

The averaging obstruction already occurs for exact commuting nonexpansive maps on [0,1]: A(x)=0 and B(x)=min(x,1/2). Then AB=BA=0, but D_A(x)=x/2, and B D_A(1)=1/2 while D_A B(1)=1/4. Hence no estimate of the new commutator solely by a multiple of the original commutator can hold. These maps share fixed point0, so this example concerns the averaging inference only.

## Graded-word repair attempt
There is a useful sharper bound for words of the normalized powers. For W=A_{m1}...A_{mr},

sup_x||W(x)−T^{m1+...+mr}(x)||≤e_{m1}+...+e_{mr}.

Replace factors starting at the right. At each replacement the prefix consists only of the exact nonexpansive A factors, and the suffix is one exact T power; hence that replacement costs at most the corresponding uniform e, with no product of Lipschitz constants. Thus convex combinations of words with the SAME total degree L remain uniformly within their maximal total error of T^L. Their mutual nonlinear Jensen defect against another such uniformly-near-power map can then be controlled through the underlying exact commuting powers.

The unresolved step is degree synchronization. The source anchor needs a convex family with arbitrary adaptive choices and finite simultaneous norm approximation. A union over degrees of the same-degree convex families is not itself convex. Mixing two degrees may be far from every single power (already alternating identity/reflection), and appending a large power to equalize degrees changes outputs without a known small displacement. Therefore this graded-word observation does not yet create the compact convex semigroup or the common terminal sequence required by the source. It identifies a possible more structured route than generic almost-commutation, but no synchronization lemma is proved.
