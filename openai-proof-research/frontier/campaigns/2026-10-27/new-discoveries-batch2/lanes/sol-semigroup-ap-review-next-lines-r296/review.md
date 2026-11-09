# Independent r295 AP review

Verdict: ordinary mathematical PASS, conditional on exact finite rational arithmetic in the prefix certificate and on the stated source sufficiency lemmas. No gap requiring correction was found. This is one restricted support, no new discovery credit, no acceptance. Counts stay 9 additional /39 total /next40; root alone accepts. The new support proofs in discovery.md require a further independent reviewer before adoption.

The r295 original is preserved byte for byte in frozen/018-discovery.md. Before reading scientific contents, freeze.py copied the r295/r294 top-level science, certificates, sources, disposition and batch administration, verified original and copy immediately, and recorded 101 flat bindings. It did not recursively copy histories. Ancestor and batch AGENTS were read first. Final verification checks every original and copy again.

## Independent ratio audit

audit.py imports none of the author modules. On the AP line it replaces monomials by pairs (d,j), 0<=d<=12, 0<=j<=2d, representing d+j(t/a). Every such pair is attainable; equality of representations preserves residue d*a+j*t modulo3. It partitions 0<=t/a<=1/2 at EVERY equality of these forms, including equality to the constant12 cutoff and the domain endpoints. On every open interval the entire order, grouping and cutoff membership are constant. Vertices are tested separately. All six possible (a mod3,t mod3) with t nonzero are checked, not just sampled integer parameters. This is a finite exact order decomposition, not a multiplicity sweep.

There are 46 events including endpoints. All surviving open intervals lie below t/a=1/9. The vertices above1/9 are exactly 1/8,2/13,1/5,1/4,2/7,1/3,2/5, hence b/a=9/8,15/13,6/5,5/4,9/7,4/3,7/5. Primitivity fixes (a,t) to the reduced denominator/numerator; only (13,2) has a>=12. It belongs to H4. The strict inequality a>9t follows for every t>=3 prefix survivor; equality would require a=9t and gcd(a,t)=1, impossible here. audit-result.json records all surviving intervals and vertices, including those BELOW the reduction threshold. This independently regenerates the needed part of r294 rather than merely rereading its assertion.

## Apéry, top gaps and run hypotheses

For AP, a coefficient j of t can occur with a coefficient q of a precisely when 0<=j<=2q. Thus minimal q=ceil(j/2); increasing j by a strictly increases the candidate. This proves A[jt mod a]=ceil(j/2)a+jt. The largest index maximizes A. Rank is the count of all residue-class arithmetic rays through n, minus zero; this proves the rank formula and its one-based convention.

Reflection about F gives, for even a, offsets ia+jt with i>=0 and 0<=j<=min(2i,a-1). For odd a, the cutoff is min(2i+1,a-1). These are gap identities only when the reflected value is positive. For even a the first offsets are 0,a,a+t,a+2t; for odd a they are 0,t,a,a+t,a+2t,a+3t. With a>9t and t>=3 these are correctly ordered; the next distances are also >=3 wherever the proof uses them. Therefore the isolated gaps used have at least two successive positive integers on BOTH sides. The top search window contains those neighboring positives. Nothing assumes a singleton positive run works.

At an isolated gap h, putting the positive member h-1 at the end of its aligned block is necessary: if its rank is1 modulo3 then (h-1,h+1,h+2) fails; if its rank is2 then (h-2,h-1,h+1) fails. Their residue patterns repeat. This proves the boundary assertion with exact ranks. For two such gaps h<h', both boundaries imply h'-h-1=0 modulo3 because all integers between the gaps are positive. The early rank7 triple independently forces t=-a modulo3. Even a then requires a=t=1 modulo3, a contradiction. Odd a requires t=1,a=2 modulo3. These deductions use successive elements, not selected nonsuccessive residues.

## Overlapping rows, endpoints and translations

Set i=ceil(a/(2t))+4 and B=F-(i+1)a. Independently substituting the odd reflected table gives row i gaps congruent B+a modulo t and row i+1 gaps congruent B modulo t. The classes differ since gcd(a,t)=1. Bounds a+8t<=2it<a+10t imply the bottom of row i is at least9t below B. Row i-1 ends above B by 2a-(2i-1)t>a-9t; earlier rows end higher. Row i+2 starts at B-a<B-9t. Thus exactly the two stated full progressions occur throughout [B-6t,B]. Saturation cannot occur: 2i+3<a for t>=4,a>9t. Positivity follows from i<=a/8+5 and a>=37, exactly as in r295; in the actual odd a=2 mod3 case the smallest possible a is41. No negative reflected gaps are used.

This window has t-2 positives per numerical period t. For any positive x in [B-4t,B-3t), its next two positive successors lie at most t above it when t=4, and at most4 above it when t>=7. (The author's bound5 is safe.) The triple and both translates by t and2t remain in the window, including their endpoints and intervening members. Exact rank increment is L=t-2=2 modulo3, so one translate starts at rank1 modulo3. Translation changes all value residues by1, preserving whether the triple is a permutation. This tests every starting phase of the infinite periodic positive word, since the central half-open interval has length exactly t.

If all sliding triples are permutations then z[j+3]=z[j]. Period t gives z[j+L]=z[j]+1, hence z[j+2]=z[j]+1 and z[j+1]=z[j]+2. There must be consecutive positive INTEGERS in the word. For t>=7 this follows because a cyclic independent set has size at most floor(t/2)<t-2. For t=4 absence would put the holes opposite, giving a=2 modulo4, contradicting gcd(a,4)=1. The consecutive pair instead has increment1, contradiction. This completes the universal row argument.

## Algorithm and sufficiency

The three windows used by ap_classifier are sufficient for every outside pair: prefix <=12a for all rejected rational strata; the top window for all top-congruence failures; the overlapping-row window for the remaining odd case. For t=1,2 the early rank7 triple (valid because a>4t) leaves only H7 and H4. Source Definition1.1 and all sixteen source generator definitions were read in frozen/099-063-1609.01133v2.txt. Lemmas4.4 and4.7 provide sufficiency; their actual statements and residue-block arguments were inspected. H4's odd-k details are abbreviated as similar in the source; this review treats the pinned source theorem as given, not as a new theorem proved here.

The independent Boolean DP builds membership directly from the three generators, through max(A)+a+8, checks the entire Apéry table, tests aligned triples, and checks that every outside pair has a failed triple inside one of the author windows. It covers 1,825 pairs (including targeted large and t=4 cases), and checks two-row gap identities wherever applicable. These are regression checks only; universal coverage comes from the rational partition and preceding proof. No bounded multiplicity evidence substitutes for a proof.

## Limits

This verdict is an ordinary proof audit with a computational dependency, not a Lean certificate or full Ugolini classification. No novelty follows from the absence of search hits. The current public proof registries were not accessed in this lane, given the explicit prohibited endpoints; no live registry clearance or novelty verdict is claimed. No shared, manuscript, Lean, git, public, browser or MathDB edits occurred. No child agents were used.
