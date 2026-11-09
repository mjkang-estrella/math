# AP support closed, conditional on the frozen r294 exact ratio certificate

This is a research proof of ONE complete support, not Ugolini Conjecture 5.1. Independent adversarial review remains required. Full-source, novelty and acceptance HOLD; no credit. Counts remain 9 additional /39 total /next40. Root alone accepts. No Lean or manuscript is supplied.

## Statement and dependencies

For every integer a>=12 and t>0 with 2t<a and gcd(a,t)=1, the semigroup G=<a,a+t,a+2t> is 3-permutation in Ugolini Definition 1.1 if and only if either t=1,a=3k+2, or t=2,a=6k+1 (k>=1). This closes the full AP parameter domain, with the following explicit upstream computational dependency, not an unqualified new source theorem.

Frozen r294 `031-lines.py` and `030-lines-result-12.json` give an exact rational one-dimensional order decomposition on the AP line, including every equality/cutoff event, all open intervals and all vertices. This necessary prefix screen uses DISTINCT positive elements <=12a, grouped equal forms and compatible generator residues. Its AP survivors have b/a<=10/9, except isolated vertices b/a=9/8,15/13,6/5,5/4,9/7,4/3,7/5. A primitive AP ratio b/a=1+t/a determines a,t uniquely. Of those seven vertices, only (a,t)=(13,2) has a>=12; the others have a<=8. Consequently every primitive pair with t>=3 which passes this frozen necessary prefix screen satisfies a>9t. Equality a=9t contradicts gcd=1. No larger-horizon arrangement or multiplicity scan was run. This certificate dependency is recorded explicitly for root review. Its derivation uses the complete finite form-order argument, not experimental sampling of parameters.

Sufficiency uses the ACTUAL frozen Ugolini arXiv1609.01133v2 Definition1.1 and Lemmas4.4,4.7, read with their proofs. Lemma4.4 constructs H4 for a=6k+1,t=2 using disjoint parity/interval blocks and verifies their residue concatenations (its odd-k argument is stated as similar). Lemma4.7 constructs H7 for a=3k+2,t=1 as successive intervals followed by a full ray; lengths modulo3 and boundary triples prove the claim. Thus these are credited source results. The new exclusion below uses only the exact AP Apéry identity established in r294, whose elementary derivation is repeated.

## Exact arithmetic conventions

G consists of qa+jt, q,j>=0, j<=2q. For 0<=j<a the least element congruent to jt modulo a is A[jt mod a]=ceil(j/2)a+jt: the least q is ceil(j/2), and replacing j by j+la, l>=0, strictly increases the candidate. Let F=max(A)-a. For n in G its positive enumeration rank is

    R(n)=sum_{r=0}^{a-1} max(0,1+floor((n-A[r])/a))-1.

Membership is n>=A[n mod a]. These formulas count zero once before subtracting it. Successive membership elements have successive ranks. In particular R(first)=1 mod3 is essential in every obstruction below.

An explicit witness is algorithmic: `ap_classifier.classify(a,t)` either returns the exact source family and k, or returns a triple of successive members, its exact rank and repeated residues. It searches three explicitly bounded local intervals in order, not increasing empirical horizons. The proof below guarantees termination with a witness on every outside pair. `check` independently verifies membership, consecutive ranks and alignment. Finite regressions support implementation only.

## A gap-cluster observation, with its needed hypotheses

A cluster of two consecutive gaps forces the positive enumeration immediately before/after the cluster to have a block boundary between them: the two consecutive semigroup members differ by3 and hence have the same residue. A single isolated gap also forces a boundary PROVIDED at least two consecutive semigroup integers occur on BOTH sides of it: a crossing aligned triple has differences (1,2) or (2,1), and repeats a residue. We do NOT apply the single-gap assertion where a neighboring positive run has length one. That tempting stronger assertion is false and is recorded as a rejected shortcut.

At the very top of the gap set, all gaps used next are isolated with neighboring positive runs of length at least two, since a>9t and t>=3. If h<h' are consecutive such gaps, boundaries before both imply h'-h-1=0 mod3, by counting the positive integers between them.

## Top gaps reduce the difficult case

The first triple requires t!=0 mod3. For a>4t, the first two degree layers lie before3a; ranks7,8,9 are (2a+3t,2a+4t,3a). If this triple is a permutation, t=-a mod3: its first two residues are 2a and 2a+t, leaving 2a+2t, which must equal0. Otherwise it is already a witness.

If a=2m is even, the top gaps in descending order begin

    F, F-a, F-a-t, F-a-2t, ... .

In particular the first gap distance a and the next distance t must both equal1 mod3 by the observation. Thus a=t=1 mod3, contradicting t=-a. Every even-a outside pair with a>9t has a witness either in the early prefix or the top window [F-a-2t-4,F+4].

If a=2m+1 is odd, the top gaps begin

    F, F-t, F-a, F-a-t, F-a-2t, F-a-3t, ... .

The first two distances t,a-t force t=1,a=2 mod3. A failure of these conditions again gives an aligned failed triple in the stated top window. We are left with odd a, a=2 mod3, t=1 mod3, t>=4, a>9t.

The lists follow directly by writing gaps as A[jt mod a]-la, l>=1. The next section gives the entire reflected table for odd a, proving there are no omitted larger gaps. The even list follows in the same way with j-distance h satisfying ceil(h/2)<=i, equivalently h<=2i.

## Two overlapping gap rows give a universal contradiction

For odd a=2m+1, F=(m-1)a+(a-1)t. Its positive gaps are EXACTLY the positive numbers

    F-i a-j t,  i>=0, 0<=j<=min(2i+1,a-1).

Indeed set the Apéry index equal a-1-j. Subtracting its minimal representative from F gives floor(j/2)a+jt, and taking further gaps in that residue increases i arbitrarily. Conversely every displayed positive value is a gap by the same residue calculation. This derivation remains valid even when rows overlap in value order; we never concatenate the rows.

Put i=ceil(a/(2t))+4 and B=F-(i+1)a. On the WHOLE integer interval [B-6t,B], exactly rows i and i+1 contribute gaps, each as a full arithmetic progression of difference t. Here are the bounds including endpoints:

* a+8t<=2it<a+10t. The bottom of row i lies (2i+1)t-a>=9t below B; row i+1 extends still further. Their j cutoffs have not saturated, since 2i+3<a for a>9t,t>=4.
* Row i-1 has its lowest value above B by 2a-(2i-1)t>a-9t>0. Earlier rows end even higher (and have smaller j cutoffs).
* Row i+2 starts at B-a<B-9t, and all later rows start lower. Thus they miss the window.
* B-6t>0: directly B=((a-5)/2-i)a+(a-1)t; using i<=a/8+5 and a>=37 gives B-6t>=((3a-60)/8)a+(a-7)t>0.

Their residues modulo t differ because gcd(a,t)=1 and t>=4. Thus membership in this window is a word periodic in numerical value with period t, having exactly two holes and L=t-2 positive integers in each period. In particular translation by t changes the positive rank by EXACTLY L, and changes the value residue modulo3 by1. Here L=2 mod3.

Take every successive positive triple starting in the central period [B-4t,B-3t). Its translates by 0,t,2t all remain inside [B-6t,B], with all intervening members there: every such triple spans at most t integer steps (for t=4 there are two positive positions per period; for t>=7 its span is at most5). Their first ranks run through all residues modulo3 because L=2. Exactly one translate is aligned. If G were 3-permutation, every such central triple would therefore represent all residues. This conclusion applies to every sliding triple of the infinite periodic membership word obtained by extending these two gap classes modulo t.

Write z_j for the positive value residues of that infinite word. Every sliding triple being a permutation implies z_(j+3)=z_j. Numerical period t gives z_(j+L)=z_j+1; since L=2 mod3 this implies z_(j+2)=z_j+1, and hence z_(j+1)=z_j+2. However the periodic word contains consecutive positive INTEGERS: for t>=7, deleting only two positions leaves such a pair; for t=4, their absence would force the two holes to differ by2, contradicting gcd(a,4)=1. Consecutive positive integers give z_(j+1)=z_j+1, contradiction.

This argument proves that at least one of the explicitly enumerated aligned triples in [B-6t,B] fails. `failed_in` returns the first one and checks its actual rank; no repeated residues from nonsuccessive elements are used as evidence. It covers every quotient, remainder, and endpoint: gcd excludes coincident progressions; strict a>9t excludes the row-boundary collision; t=4 was separately handled.

## Completing the support and retaining the remaining problem

If t=1 or2, a>=12 implies a>4t; the rank7 triple forces a=-t mod3. For t=1 this is exactly H7. For t=2 primitivity forces a odd, so a=1 mod6, exactly H4. For t>=3 use the frozen ratio reduction, dispose of even a with the top gaps, and odd a with the two-row argument. All parameter pairs are covered, subject to the explicitly stated r294 ratio-certificate dependency.

The other NINE supports remain unresolved, including BOTH next priorities. For <a,2t,3t>, 3t/2<a<2t, gcd(a,t)=1, writing s=2t-a, the conjectural necessity s in {1,2} is not proved here. Source H2 is s=1,t=3k+1; H15 is s=2,t=6k+5. For <a,a+t,3t>, a/2<t<2a/3, source H3 has 2t-a=1,a=6k+1,t=3k+1; H16 has 2t-a=2,a=12k+8,t=6k+5. Those are source formulas, not a proved exhaustive list. Their exact r294 Apéry tables and rank formula still give the universal residual: exhibit a successive aligned failed triple for every primitive outside-source pair, or find a fully conductor-certified counterexample. No full-source PROOF.md is warranted.

Root target provenance: frozen `004-STATUS.md` proposed this intermediate AP classification as an unproved target. We do not attribute that conjectural necessity to Ugolini as a separate theorem. Ugolini's actual source contains sixteen constructions and the full classification conjecture. This restricted support is uncredited progress toward that endpoint, with no novelty claim.
