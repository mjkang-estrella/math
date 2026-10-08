# H007 CARRY-LP-v1: frozen candidate for symbolic review

Native Astra /root/h007_lattice_carries proposed and froze this circuit.
Independent /root/h007_additive_relations reviews correctness and fractional
feasibility. No implementation, numerical diagnostic or Lean proof authorized.
Verified ECDLP improvement NONE. This is a full-range exhaustive solver with
a speculative early-pruning heuristic, not an efficient attack.

## Total exact circuit

p>3, E:y²=x³+Ax+B, generator G of odd prime order n>2. Return0 ifQ=O.
Finite point representation(x,y,0), infinity(0,0,1), canonical field wires0..p-1.
L=ceil(log2 n). MSB-first binary scalar loop starts R0=O. Stage i:
D=double(R), U=addG(D), Rnext=mux(b_i,D,U).
Precompute G2=2G=(x2,y2), charge it. All0<=k<n, leadingzero bits included.

inv(a)=a^(p-2), includinginv0=0, fixed ordinary left-to-right public binary chain:
accumulator a, then square for every remaining exponentbit, multiply bya ifbit1.
r=bitlength(p-2)+popcount(p-2)-2 modular multiplication gates.

Doubling input(x,y,o):
d=2y; v=inv(d); a=x²; lambda=(3a+A)v;
xstar=lambda²-2x; ystar=lambda*(x-xstar)-y;
z=dv; H=(1-o)z;
xD=H*xstar; yD=H*ystar; oD=1-H.
Flags z,H,oD declared Boolean-valued in exact executions.
Ordinary finite doubling, y0=>O, infinity=>O.
r+8 multiplication gates and5 modular affine gates.

Fixed-G addition input(x,y,o):
d=x-xG; e=y-yG; v=inv(d); w=inv(e);
H=dv; T=1-ew; lambda=ev;
xstar=lambda²-x-xG; ystar=lambda*(x-xstar)-y;
S=(1-o)H; J0=(1-o)(1-H); J=J0*T; oU=J0*(1-T);
xU=S*xstar+J*x2+o*xG; yU=S*ystar+J*y2+o*yG.
Flags H,T,S,J0,J,oU Boolean-valued in exact executions.
Cases infinity=>G; finite d!=0=>usualsum; d=e=0=>2G;
finite d0,e!=0=>O (input-G). Costs2r+11 multiplication gates and7 modular
affine gates; multiplication by fixed constants is part of affine gates.

For each coordinate v=x,y,o, integer selector:
a_v=(1-b)vD; c_v=b*vU; vR=a_v+c_v.
Six non-modular products. Flag complements use integer subtraction.
Every point-state has0<=o<=1 and0<=x,y< p withx,y<= (p-1)(1-o).
No additional curve identities/cuts. Endpoint R_L=(xQ,yQ,0).
Scalar bounds0<=b_i<=1 andsum2^(L-1-i)b_i<=n-1.

## Frozen relaxation and deterministic search

Depthfirst MSB-first, child0before1. Branch ONLY scalarbits.
One forward topological simplification after prefix/endpoint substitution:
evaluate gates with all operands known; multiplication0/1 and affine identities;
knownmuxbit identifies output withselectedinput; conflictingconstants infeasible.
No LP-derived bounds, backwardnonlinearpropagation, probing, adaptive cuts.
Remaining field wires [0,p-1], declaredBooleanwires [0,1].

Modular product: introduce realW, outputz, carryc, W=z+pc. Four McCormick
inequalities for operand intervals[lx,ux],[ly,uy]:
W>=lx*y+ly*x-lx*ly; W>=ux*y+uy*x-ux*uy;
W<=ux*y+ly*x-ux*ly; W<=lx*y+uy*x-lx*uy.
Carry bounds ceil((minxy-uz)/p)<=c<=floor((maxxy-lz)/p), but RELAX integrality.
Square gate uses repeated-input envelope:
W>=2lx*x-lx², W>=2ux*x-ux², W<=(lx+ux)x-lx*ux; no other tangents.
Modular affine f=z+pc retains equality, with analogously integer-rounded
interval bounds onc, then relaxedc. Integer muxproducts use ordinary McCormick,
no carries. Unassigned bits and Booleanflags also continuous.

Exact rational LP feasibility; prune ONLY certifiedinfeasible. Otherwise descend.
At each complete assignment evaluate kG exactly and compareQ, regardlessLP.
Every true execution satisfies envelope, so a correct infeasibilitycertificate
must preserve the secret. Floatingpoint infeasibility alone is insufficient.

## Size and complete cost

Perstage3r+19 modular multiplications,12 modularaffine,6 integermux products,
plusO(1)flag complements/state equalities. SizeO(L logp), coefficientbitsO(logp).
At256bitp r<=510; L256 gives396544 modularmultiplicationgates beforeconstant
simplification, plus1536integerproducts. This is a gatecount bound, not runtime.
Paysetup/fixedbasepoints, propagation, everyLP/certificate, allfailedbranches,
reconstruction/storage andfinalverification. WorstcaseO(n)searchnodes.
To improveexponent withpolynomialnodecost requires2^((1/2-epsilon)L) nodes.
Fewerthansqrt(n) LPnodes alone doesNOTestablish a practical fullcostwin.

## Proposer's exact local defect

M=p-1,t=M/2. An unassigned inverseinput can take valuet while its interval
remains[0,M]. Set everyaccumulator tot. Each product then hasinputs(t,t),
outputt,W=t,c0; envelope permits0<=W<=M²/2. Allvalidforp>3.
At finalnonzeroflag z=a*inv(a), setW=z=c0 despiteinputst,t.
Thus a nonzero input can return zeroflag. Even these witnesswires/carries
are integral; integrality alone doesn'trepair the relaxed product equation.

This is a STANDALONE gadget witness, not simultaneous wholecircuit feasibility.
Independent reviewer must either compose endpoint-respecting witnesses through
enough unknownbits to defeat the costgate or state the exact remaininggap.
No heuristic/cut tuning or solver implementation follows automatically.

## Prior art and disposition

McCormick relaxation is established globaloptimization:
https://link.springer.com/article/10.1007/BF01580665
Proposer inspected abstract only, fulltextsubscriptionrestricted.
Coppersmith's inspected primaryabstract supplies no growingdimensional fullrange
root guarantee: https://research.ibm.com/publications/small-solutions-to-polynomial-equations-and-low-exponent-rsa-vulnerabilities

Related discarded ideas: lowheight rational lifts need an explicit inexpensive
dependence construction; finitefield dependence doesn'timply rational dependence.
Carry-only Coppersmith needs actualmonomials/scaling/latticedeterminant/extraction;
ordinary productcarries have sizep, and limbing introduces morevariables.
No newcard orLLLtest from that missingprimitive.
