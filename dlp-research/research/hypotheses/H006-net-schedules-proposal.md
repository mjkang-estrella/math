# H006 P2 exact schedules: proposer ledger for independent review

Native Sol /root/h006_net_cost_development supplied this mathematical cost ledger,
read-only, no experiments/edits/children. Raw/quotient schedules are known-type
net arithmetic; no novelty/exponent claim. Counts below are PROPOSED, not yet
accepted after independent review. M,S,I,A_f denote field operations; small
integer constants must be implemented/charged explicitly, not free arbitrary M.

Curve y^2=x^3+A*x+B, p>3, odd prime subgroupq>5, G=(g,h),h!=0. Let
alpha=4h², beta=-psi3(G)=-(3g^4+6Ag²+12Bg-A²), J=6g²+2A.
beta also equalsalpha*(x(2G)-g). For P_n=P+nG, normalized net coordinates obey
x(P_n)=g-w_(n+1)w_(n-1)/w_n² and
w_(n+2)w_(n-2)=alpha*w_(n+1)w_(n-1)+beta*w_n².
Compute full P+G; d0=g-x(P), d1=g-x(P+G); seed
w_-1=d0,w0=w1=1,w2=d1. This is a geometric row gauge c*t^n preserving ratios
and recurrence. Require finite seeds,d0d1!=0; exceptional points handled separately.

Independent review correction: the first raw quartet is centered at n=1 and
emits x1,x2,x3,x4. The seed already supplied x1, so only THREE outputs per stream
are new in this startup quartet. The generic four-output ledger below is valid
for subsequent regular blocks, not a four-new-output startup claim. Beginning
at n=2 instead requires a separately charged warmup and inverse-cache dependency.
The quotient schedule first emits x2 and has no such duplicate.
Primary coordinate identity: Stange Lemma3.5 https://arxiv.org/pdf/0710.1316
Translated Somos prior art: Hone DOI10.1112/S0024609304004163.

Seed generation P=aG+bQ is charged. R independent streams may require R such
seeds. Batched full P+G for R regularseeds costs I+(5R-3)M+RS+6RA_f;
two d-values add2RA_f. Seed x outputs may be used, but must not be counted twice
in a matched output stream. Index alignment and seeding are review obligations.

## Raw terms and cached inverses

p_n=w_(n+1)w_(n-1),s_n=w_n²,
w_(n+2)=(alpha*p_n+beta*s_n)/w_(n-2), x_n=g-p_n*(1/w_n)².
Given cached inverses, regularcost5M+2S+2A_f per center. Four births can precede
refresh for recurrence, but only first TWO coordinate outputs use old inverse
cache; last two outputs require inverses of first two newborn terms. Store their
products, invert four births across R streams, then emit deferred outputs.
Continued block4R outputs: (32R-3)M+8RS+I+8RA_f.
Peroutput8M+2S+2A_f+(I-3M)/(4R).
Initial inversecache of d0,d1: I+(6R-3)M, two unit inversesknown.
Constants throughaffine2G: I+3M+3S plus smallconstantadditions (or paid polynomial).

Terminal block4R outputs: omit unused FOURTH recurrence birth, invert only first
two newborns to supply last two coordinates. Cost(23R-3)M+7RS+I+7RA_f.
T blocks: (T-1)continued+terminal+seeds/setup/joins/exceptions/recovery.
An earlier provisional claim that all final inversion could be skipped was
withdrawn by proposer after dependency tracing; do not use it. Straightforward
storage16R fieldwords (4terms+4inverses+4prefix+4outputs/products), plus labels/table.

## Quotient recurrence

d_n=g-x(P_n). Its multiplicative identity is
d_(n+1)d_(n-1)=(alpha*d_n+beta)/d_n².
Additionlaw also givesd_(n+1)+d_(n-1)=J/d_n-alpha/d_n².
Withr_n=1/d_n, update d_(n+1)=(J-alpha*r_n)*r_n-d_(n-1), outputx=g-d_(n+1).
Kernel2M+3A_f. Across R streams, emit/check outputs before inverting R new d's
ONLY if continuing. Continuedround(5R-3)M+I+3RA_f; terminal2RM+3RA_f.
T rounds:2TRM+(T-1)[I+3(R-1)M]+3TRA_f.
Seedfullpoints,d0,d1,initiald1batchinverse andconstants(2S+smalladds) paid.
One-step inverse dependency means larger R requires more independent seeds.
Straightforward5R fieldwords (two d,currentinverse,prefix,output), plus labels/table.

## Strong known comparator

R full affine centers C, offsets T_j=jG,j1..h, advanceD=(2h+1)G.
Emit centerx and x(C+/-T_j), thenadvancecenterD. Pair uses common
Delta=x(T_j)-x(C), slopes(y(T_j) minus/plus y(C))/Delta and x=slope²-x(C)-x(T_j).
Paircost2M+2S+6A_f withoutinversion; centeradvance2M+S+6A_f.
BatchR(h+1) denominators once. L=R(2h+1) outputs percontinuedblock:
(5R(h+1)-3)M+LS+I+6R(h+1)A_f.
RegularM coefficient tends2.5/output; h1 gives10M/3+S+4A_f+(I-3M)/(3R).
Successivelyforming2G..(2h+1)G precompute:2hI+4hM+(2h+1)S plusadds/exceptions;
better known precomputation allowed. Straightforward workingwords
2R+2(h+1)+3R(h+1)+L plus labels/collisiontable.

At an UNFORESEEN terminal collision, skip centerarithmetic2RM+RS+6RA_f, but
cannot retroactively remove R centerdenominators from the combined inversion.
Separatecenterinversion must be paid if deferring it; known-lastblock can omit it.
An earlier provisional claim omitting those denominators was withdrawn.
Primary known baseline: Galbraith-Wang-Zhang
https://pdfs.semanticscholar.org/5753/7e7d4d08b6de01aa79717c4bb849e694958f.pdf
Terminalsatellite-yomission also in existing primarykeyhunt.cpp (not new):
https://raw.githubusercontent.com/albertobsd/keyhunt/main/keyhunt.cpp

Give quotient L independentstreams optimistically to match L outputs/oneinverse.
Proposed continued arithmeticexcess:5RhM-LS-3RA_f.
Forh1: R(5M-3S-3A_f)>0 if S<=M andA_f<2M/3. Rawlosesmore.
This comparison gives quotient additionalstreams despite seedcost; it is only
regulararithmetic, not automatically every finite stopping-time solver cost.
Match outputsets/order/batchsize, exceptiontreatment and memory before comparison.
No measured hardwarecost follows from arbitrary fieldweight choices.

## Recovery and exceptions

Labels(a_i,b_i),(a_j,b_j), sign eps=+/-1 yield
k=-(a_i-eps*a_j)/(b_i-eps*b_j) modq when denominatornonzero; verifykG=Q.
Charge scalarfieldarithmetic and upto2 verifications. Common to xonlycomparator.
Orientation recovery alternative withadjacentcoords:
y(P_n)=(x(P_(n-1))-x(P_(n+1)))*d_n²/(4h), costS+2M+subtraction
withfixedinverse4h paid; adjacentcoords retrieval/regeneration notfree.

w_n=0 impliesP_n=O; d_n=0 impliesP_n=+/-G. For P_n=(a+n)G+bQ,b!=0,
recover directcandidates k=-(a+n)/b or(+/-1-a-n)/b, thenverify.
Proposer used -n/b in shorthand; root explicitly retains offseta. Knownb0rows
can avoidbadseedindices. Continuation needschargedfullpointandreseed, neverinverse0.

Total=setup+generation+joins/sorting/hash+labels+exceptions+recovery+restarts.
No justifiedcollisionprobabilitygain. Checking only after L outputsbounds extra
outputsbyL-1; expectedhalfovershootneedsuniformpositionassumption. No numerical
pilot warranted unless an independently reviewed favorable completecost survives.
