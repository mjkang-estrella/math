# Retaining one thousandth of the source separation surplus

Author proof reuse, prompted by the parent's observation of strict scalar margins. This is not an audit of the stipulated source estimates and not an independent review. All source decimal bounds are taken as exact rationals. Actual reads: scalar.tex253 through its end, plus1–100; matrix.tex155–205 and478–590; transport.tex85–110 and355–395. Earlier source derivative properties and final chaos remainder were also read.

Set eta=1/1000. In the source two-endpoint proof, put

 t=|log q(a_+)-log q(a_-)|,
 Theta_m(t)=(1+m)/4 * (1+t²/30+t⁴/1680)/(1+t²/36).

The source proof bounds the increment coefficient by

 t²(1+t²/36) max(P_-,(P_-+P_+)/2)/4.

It suffices to replace every source threshold comparison by

 max(P_-,(P_-+P_+)/2) <=(1-eta) Theta_m(t).             (S)

Every case of the actual proof permits this replacement:

* R1: the left side is at most .3425, below .999*.345.
* U1,V1: at most .31, below .999*.42.
* T1: at most .39, below .999*.42.
* P1 with upper endpoint<=-1: at most .20, below .999*.2975.
* P1 crossing -1 with t<=4: at most .284143, below .999*.2975.
* P1 with4<=t<=5: below .345394, below .999*Theta_.19(4).
* P1 witht>=5: at most .38105, below .999*Theta_.19(5).
* O with the whole interval<=-1 andt<=4: both endpoint bounds are at most max(.144+.011*4,.20)=.20, below .999*.25.
* In the same O case witht>=4, the upper endpoint cost is at most max(.144+.011t,.20). The constant .20 is already covered. For the other cost use the source Theta_0(t)>=.25+.00260t². The difference after retaining eta is

  .10575-.011t+.0025974t²,

  a strictly positive quadratic, since its leading coefficient is positive and its discriminant is negative.
* O crossing -1 has t>=4 and P_-=.156+.031t-.368/t. Again use the source quadratic lower bound for Theta_0. The difference is

  .09375-.031t+.0025974t²+.368/t.

  The quadratic part alone is strictly positive by its negative discriminant. If the upper endpoint is not T1, its cost<=.23 is below .999*.25. If it is T1, t>6.5 and its cost<=.39 is below .999*Theta_0(6.5).

These cases cover all ordered endpoint positions, with the source endpoint conventions. Theta_m is increasing, as established in the source. At coincident endpoints the separation term is zero, so the unchanged local surplus is sufficient. The script separation-slack-check.py certifies all finite rational comparisons and the two discriminants, and verifies that eta=1/100 would fail the R1 comparison. No numerical sampling is used.

Thus the source proposition mat:scalar-pair strengthens, with every other term unchanged, to

 endpoint quadratic <= Q(G,g-G/2)+(1-eta) r_ij t² Z².   (P)

Here r_ij=(1+m0(min(a_i,a_j)))(1+t²/30+t⁴/1680)/16, exactly the source weight.

## Carrying the saved term through the actual proof

The source pre-pair inequality contains -C_sep. Substituting(P) instead of the displayed source pair bound returns only +(1-eta)C_sep. Therefore -eta C_sep remains. C_sep is exactly

 E sum_(r,i,j) r_ij |log q(a_i)-log q(a_j)|² |(partial_r A)_ij|².

The derivative-index rotation and matrix pairing are unchanged. No eigenvectors are differentiated and no comparison to a compressed pencil occurs.

The same proof can retain its covariance supporting-plane gap

 G=tr(S C)-logdet(S C)-m>=0,

because the sole replacement logdet C+m<=tr(S C)-logdet S discards exactly G. In the notation mathscrD=-2delta this adds -G to the pre-pair bound.

Finally at Gaussian chaos degree d>=2, the source final polynomial supplies coefficient

 k_d=1/500+(d-2)(1+68/d)/50

in front of ||Y_d||². Its excess over d/1000 is exactly

 k_d-d/1000=(d-2)(19d+1360)/(1000d)>=0.

Summing the convergent H1 chaos decomposition gives the simultaneous all-deficit estimate

 2delta >= G + ||gradient Y||²/1000
                 +Omega(B)/1000+C_sep/1000.           (R)

The separately displayed source bound ||Y||²<=1000delta remains available; alternatively the absence of chaos0,1 gives ||Y||²<=||gradientY||²/2. This is a retained paid remainder, not a new theorem with a new source hypothesis. Source smoothness assumptions remain in force here; the full entropy candidate's approximation passage is a separate obligation.
