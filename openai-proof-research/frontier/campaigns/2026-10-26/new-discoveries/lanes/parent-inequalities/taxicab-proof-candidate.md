# PROVISIONAL proof route for341671: universal normed-space3/2 bound

Not counted; novelty/literature and independent proof review incomplete.

After translating interior point to0, let vertex vectorsa,b,c havepositivebarycentrics λa,λb,λc sum1 andweightedvector sum0. PutA=||a|| etc andr_a=distance0tolinebc. Then
r_a≤min(B,C, λa A/(1−λa)), cyclically: endpoints givefirst2bounds, whilelinebc contains−λa a/(1−λa). Consequently λa≥r_a/(A+r_a), soΣ r_a/(A+r_a)≤1.

Pure scalar claim: for A,B,C>0 andu≤min(B,C),v≤min(A,C),w≤min(A,B), ifΣu/(A+u)≤1 thenu+v+w≤(2/3)(A+B+C).

Proof candidate sortA≤B≤C andsupposesumt>2S/3. Scalingu,v,wdownifneededreduce t=2S/3. The capacities are(B,A,A), andt≥A+B≥2A. Theconcavefunction F(u,v,w)=u/(A+u)+v/(B+v)+w/(C+w) hasminimumoverbox∩sum=t atavertex,where2componentsatsaturatedupperbounds(nocomponentcanbe0exceptboundarycase). Threevertices:
V1=(t−2A,A,A): F≥1 equivalentu(2A+B+C)≥BC−A², whose numeratorafteru=2(B+C−2A)/3 is[2B²+BC+2C²−5A²]/3≥0.
V2=(B,t−A−B,A): putv=(2C−A−B)/3. v/(B+v)≥(C−B)/(B+C) becausecrossproductdifferenceB(B+C−2A)≥0. Also(C−B)/(B+C)≥A(C−B)/[(A+B)(A+C)] because(A+B)(A+C)≥A(B+C). This givesF≥1.
V3=(B,A,t−A−B): first2termsB/(A+B)+A/(A+B)=1, lastnonnegative.

Forstrictsumt>2S/3, scaleallcoordinatesbyfactor<1 tothreshold. Fstrictlydecreaseswhenpositiveuiv (A>0), soF>1 contradiction. Ifthresholdboxemptyclaimtrivial. ThusboundholdsforANYnormedspace(triangleliesaffineplane), notonlyL1. Thiswouldresolve341671ifcorrectandnotknown. Needcarefulvertices/existence/concavityargument andboundaryu=0cases, provecompleteformalbridgebeforecount.

Numericalsearch1.2milliontaxicabtriangles foundminratio1.5343≥1.5; auxiliaryabstractboxsearch1milliontriplesno violations. Neitherisproof. The analytic3vertexargument above is provisionalmathematicalproof.


## Simplex clarification

For threshold sum t=2(A+B+C)/3 and capacities (B,A,A), put D=B+2A-t. Feasibility implies D≥0, while C≥B≥A implies t≥A+B and t≥2A, hence D≤A≤B. Deficits (B-u,A-v,A-w) are nonnegative and sum D. If D=0 the threshold slice is a single point. If D>0 every point is the convex combination of V1,V2,V3 with weights (B-u)/D,(A-v)/D,(A-w)/D. Concavity therefore reduces the scalar inequality exactly to the three displayed vertex checks, without relying on an unstated polytope theorem.
