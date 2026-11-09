# Ordinary primary-proof comparison: MathDB 335255

Recommendation: ORDINARY PASS ADOPTED; OVERALL HOLD. Credit 0; campaign 52/60 unchanged. No acceptance or Pi authorization. This is an ordinary reading of mathematical declarations, not a verification of their Lean implementation.

## Endpoint and inherited findings

For every real alpha>0, Fish's cached Conjecture 1 asks for bounds N,k depending only on alpha such that every finite commutative R of size at least N and every E of size at least alpha|R| have a subring S contained in the SINGLE setwise product P(E)=(E-E)(E-E), with |R|/|S|<=k. The adopted independent review proves its full negation at alpha=1/2 using nontrivial unital rings F2 ⊕ F2^m, even with permissive nonunital subrings. Cached-original fidelity and ordinary full-refutation PASS are inherited, not upgraded to final-version fidelity. Read the completed review, ID-keyed verdict, routing and parent integration; author BRIEF finite-ring mechanism lines16–40 was separately recovered after a truncated batch display.

## O1: LeanPool Quantitative — precise bounded nonmatch

Source: `fresh/LeanPool-Quantitative.lean`, immutable c8e32730bbee854797f77b247fdfadf2eaf3720b; full143 lines read. This is a proof body, not just the previously read stub. Namespace SumDifferenceExponent. Definitions quantitativeScale=10^999 (21), quantitativePower=100*quantitativeScale (24), powerOfTwo(n)=2^n (28), quantitativeIndex=powerOfTwo quantitativePower (37); quantitativeSet : Finset Z = approximatingSet quantitativeIndex (40–41).

The exact public terminal declaration is quantitative_example (131–141):
  2 - (10:real)^(-999:integer) < growthExponent quantitativeSet
  AND growthExponent quantitativeSet < 2.
It has no additional theorem parameters or assumptions: a particular finite integer set is supplied. exponentLower_quantitative (107–129) bounds ColumnConstruction.exponentLower at that index by the same lower threshold. Auxiliary quantitativeScale_pos, quantitativePower_pos, quantitativeIndex_two_le, log_constant_lt_twenty_three, quantitative_denominator_gt and forty_six_div_quantitativePower_lt prove positivity/logarithmic inequalities, not ring statements. The enormous exponents were read symbolically, never evaluated.

Explicit import Main was read in full (82 lines). approximatingSet(l) is ColumnConstruction.A(l), a Finset Z (19–20); approximatingSet_card_two_le assumes l>0 (22–25); exponentLower_le_growthExponent_approximatingSet assumes l>=2 (27–31). tendsto_growthExponent_approximatingSet (37–46) states convergence to2 as l tends to infinity. admissibleExponents={x | exists B:Finset Z, 2<=card B and x=growthExponent B} (49–50); isLUB_admissibleExponents, sSup_admissibleExponents and supremum_not_attained (53–80) say its supremum is2 and every B with card>=2 has exponent different from2.

Main imports Limit, also read in full (161 lines). exponentLower(l)=log(l^2/2)/log(12l) (21–22). sigma_A_lower assumes l>0 and proves l^2/2<=sigma(A l) (31–52); its proof unfolds sigma into |A+A|/|A|. delta_A_upper assumes l>0 and proves delta(A l)<=12l (54–72); its proof unfolds delta into |A-A|/|A|. exponentLower_le_growthExponent_A assumes l>=2 (74–112); its displayed unfolding identifies growthExponent(A l) as log(sigma(A l))/log(delta(A l)). exponentLower_formula assumes l>0 (114–125); tendsto_exponentLower is a limit at infinity (135–159).

Thus the actual proof is about ratios of additive sum/difference cardinalities for finite subsets of Z. Multiplications such as l^2 and 12l are scalar arithmetic on cardinal bounds, not products of elements of E-E. There is no variable finite commutative ring, no multiplication on an arbitrary additive group, no subring, fixed-density ambient-ring family, nilpotent example or Fish refutation in these three inspected bodies. The proof's denominator uses delta>1, obtained from strict difference-set growth in Z. For the proposed nilpotent ideal E, E-E=E instead, so delta=1 and this positive-log argument does not specialize. An integer finite set also cannot simply be identified with a growing exponent-two additive group preserving its additive cardinalities.

Missing bridge: an additive-cardinality statement would need an additional assertion controlling the specified ring multiplication and a contained subring with uniformly bounded ambient additive index. None is supplied. No subsumption reduction is asserted. Limit imports Construction and Basic, whose bodies remain unread at the four-GET cap; no claim about every declaration in that transitive library is made. Their named uses visible here are additive cardinality estimates. This is enough to resolve the scope of quantitative_example, not to certify absence of other results elsewhere.

O1 verdict: CONCRETE DECLARATIONS NONMATCH; no ring-product consequence established. Registry-wide clearance is not claimed.

## O2: TauCeti extension — actual declarations and applicable import

Source: `fresh/TauCeti-TrivSqZeroExt.lean`, immutable08a51bc861c1164cec8967d78702731083676e5d; full95 lines read. Common assumptions (45–46): R,M are types; R a commutative ring; M an additive commutative group with left R- and opposite-R-module actions and central scalar compatibility. No finite-cardinality, density, threshold or Fish hypothesis occurs.

Within the additional assumption IsLocalRing R (50):
* isLocalRing (53–55) makes TrivSqZeroExt R M local, using the imported criterion that an element is a unit iff its first coordinate is.
* mem_maximalIdeal_iff (59–61), for every x, characterizes membership by x.fst in maximalIdeal R.
* isLocalHom_algebraMap (65–66) says the base inclusion is a local homomorphism.
Outside that section:
* the instance (71–72) assumes Module.Finite R M and concludes Module.Finite R (TrivSqZeroExt R M). Here finite means finitely generated MODULE, not a finite carrier or an absolute cardinal bound.
* (75–76) adds IsNoetherianRing R to conclude the extension is Noetherian.
* Algebra.IsIntegral (80–85) has only the common assumptions and proves every element integral by writing it as base image plus a square-zero element.
* FaithfulSMul (88–89) uses injectivity of the base inclusion.
* ringKrullDim_eq (92–93) asserts equal Krull dimensions through the explicitly imported integral/faithful dimension theorem.

The header's references to depth_eq_zero and not_flat (28–30) have NO corresponding declarations in this body. They are not taken as proved here. The imported KrullDimension.Integral theorem is not a possible density/subring bridge; its proof was not fetched merely to audit dimension infrastructure irrelevant to Fish.

The mathematically applicable import is Mathlib.Algebra.TrivSqZeroExt.Basic. Its exact local body under the authorized 2026-10-14/formal/.lake/packages/mathlib path was read as ordinary source (1125 lines; initial large display truncated its middle, then relevant399–700 recovered fully). SHA256 c0d0fe06681fe12e647b319e55bbcaa256b68de1e7dbdf0c64aa91d75042c39e. Do not infer that TauCeti's dependency pin is this identical local revision: no dependency resolution was performed.

Relevant actual construction/declarations:
* TrivSqZeroExt R M is definitionally the carrier R x M (69–70); inr(m)=(0,m) (89–90), injective with Zero R (165–166).
* addition/subtraction/negation are inherited componentwise (185–192); addCommGroup with additive commutative group factors (217–218). inr_sub assumes SubNegZeroMonoid R and Sub M and says inr(m1-m2)=inr m1-inr m2 (352–354).
* mul (409–410), under Mul R, Add M and both scalar actions: (a,v)(b,w)=(ab,a acting on w + v acted on by b). With symmetric field actions this is exactly (ab,aw+bv).
* inr_mul_inr (454–457), for any semiring R, additive commutative monoid M and both module structures, says inr m1 * inr m2=0 for ALL m1,m2, not just equal vectors.
* commRing (665–666) assumes CommRing R, AddCommGroup M, both modules and IsCentralScalar R M. This proves precisely the ring structure used in the adopted example, for arbitrary module rank.
* one=(1,0) (406–407); nontriviality inherited from a nontrivial base (244–246).

O2 body verdict: STRUCTURAL INFRASTRUCTURE, NOT AN EXPLICIT FISH REFUTATION. Nonetheless the imported construction is directly applicable: it supplies the whole structural mechanism, not a merely analogous algebra name.

## Complete construction-to-Fish endpoint reduction

This is ordinary reasoning from that construction; it is NOT a claim that the source itself states these density or quantifier conclusions.

1. For every positive integer m, take the field F2 and its module V_m of all functions {1,...,m}->F2. Give the opposite action the same scalar multiplication; centrality and the commuting-action hypotheses follow from commutative field multiplication. Set R_m=TrivSqZeroExt F2 V_m. The construction above gives a commutative associative unital ring with carrier F2 x V_m and identity(1,0) distinct from zero. No local, Noetherian or Krull-dimension theorem is needed.
2. Set E_m=inr(V_m). Injection identifies it with V_m. Counting independent binary coordinates gives |V_m|=2^m; counting carrier pairs gives |R_m|=2^(m+1), |E_m|=2^m, hence exactly density1/2. This is elementary symbolic counting, not a computation run. Importantly, enlarging MODULE RANK leaves the base size fixed, so density is fixed while |R_m| is unbounded.
3. The inr subtraction identity gives E_m-E_m subset E_m. Since zero is in E_m and x=x-0, equality holds. The all-pairs inr_mul_inr identity gives P(E_m) subset{0}; choosing four zeros gives equality. It is the single product of differences, with no span or sum replacement.
4. Any permissive subring S inside{0} contains zero and therefore equals{0}, has cardinality1 and index |R_m|. If S must contain ambient1, no such S exists, since(1,0)!=(0,0); excluding zero rings likewise cannot rescue existence.
5. For arbitrary proposed finite real bounds N,k, choose a positive integer m>max(N,k,1) by the Archimedean property. The elementary induction 2^(m+1)>=m+2 gives |R_m|>N and |R_m|>k. Thus the antecedent holds but every permissive S has ratio |R_m|/1>k; under ambient-unital conventions there is no S. Natural bounds are included by real embedding. This proves forall N,k exists R,E violating the conclusion at ONE alpha=1/2, exactly negating forall alpha>0 exists N,k forall R,E.

There are no remaining mathematical bridges in this ordinary reduction. No new ring construction, normal form, dimension result, incidence bound or density theorem is required beyond the prior split extension and the displayed counting/subtraction argument.

## Routine-adaptation objection, strongest contrary case, chronology

This comparison materially strengthens the objection: the candidate's entire family, multiplication and vanishing all-pairs radical products are exactly instances of an existing general construction, with arbitrary rank already allowed. The extra endpoint work is explicitly steps2–5 above: fixed-base counting, image subtraction, singleton subrings and unbounded rank. This is a COMPLETE construction reduction, not an exclusion justified by familiarity, shortness, library use or ease alone. It is a substantial basis for root to consider routine-adaptation exclusion under the written standard.

Strongest contrary assessment: an old construction need not make every new application scientifically routine. Neither TauCeti nor inspected mathlib states the positive-density uniform-bound obstruction or even mentions Fish. Selecting a fixed base with unbounded module rank exposes precisely a degeneracy absent from the conjecture and survives nontrivial/unital-ring and subring conventions; it is more than a fixed parameter instance or an endpoint correction. Calling every inference from standard algebra routine would wrongly exclude real mathematical discoveries. The critical question is whether this particular identification and elementary endpoint transfer meet the campaign's substantive threshold; absence of a Fish filename cannot answer it either way.

Adjudication: record COMPLETE_CONSTRUCTION_REDUCTION and a concrete routine-adaptation objection; retain routine/significance adjudication HOLD rather than declare a proved earlier public Fish solution or impose exclusion solely from infrastructure. The previous review's *missing complete bridge* objection is resolved mathematically here. Its recommendation cannot simply be repeated as though no bridge were available. No affirmative novelty/significance PASS follows. Root retains adjudication authority.

Chronology: inherited source review records arXiv v1 8Feb2017/v2 13Feb2017 and final Fish electronic publication2May2018. Its observed LeanPool head has patch date6Nov2026 and TauCeti head7Nov2026; those are previously observed head dates, not separately authenticated introduction dates for these particular declarations. Fresh retrievals here occurred7Nov2026 UTC (6Nov Los Angeles) at the exact requested hashes; no head refresh or history query. They are present counterparts, not shown to predate the original Fish question. The mathlib Basic header says Copyright2020 and names its authors; this supports the library's historical attribution, but does NOT prove the first publication date of every current declaration or authenticate this local revision as public before the candidate. No git/history/dependency work or claim of exact declaration introduction chronology was made. Even a construction from2020 could predate our2026 application while postdating Fish; these two chronological comparisons must not be conflated. This bounded lane does not settle public priority or final novelty.

## Gates, residuals and access

Ordinary full refutation PASS adopted. Cached-original fidelity PASS adopted. O1 concrete nonmatch resolved; O2 infrastructure status and mathematical reduction resolved. This is not exhaustive registry clearance; generic unread directories remain coverage limits, not demonstrated subsumers. Prior HOLD; novelty HOLD; significance/routine HOLD with the above explicit objection; final-source fidelity HOLD. Proc.AMS146(8)3449–3453 DOI10.1090/proc/14078 final mathematical body/corrections remain unread. None of the four inspected remote files cites a new lawful final/accepted Fish file. No final-source request was made, no exhausted searches or AMS/login route repeated. Formal endpoint, axiom audit and extracted replay NOT_AUTHORIZED/NOT_RUN. Any Pi consideration remains DORMANT, no dispatch, execution or acceptance.

Exactly4 fresh direct GETs, all200 at their requested final URLs, zero search batches. Detailed UTC/status/bytes/hash receipts and full source bytes are on disk. The additional GETs followed explicit mathematical imports Main and Limit to resolve the terminal additive result; the cap prevents reading their Basic/Construction interiors. No browser, service API, POST, contacts, proxy, bypass, TLS weakening, installation or mathematical execution. No protected lane, broad history scan or shared/author/parent/paper edit.

236 frozen bindings passed before mathematical reads; frozen-after is independently recorded after writing these judgments. All command readers set affinity<=2 CPUs, CPU<=120s, AS<=6GiB before file reads; external timeouts<=140s; Python-I-B throughout. Writer children inherit limits and additionally set CPU10s/AS512MiB; controllers sample their RSS every10ms with512MiB kill and20s wall guards, join guard threads and communicate/reap children. Writers spawn no descendants. A sampled zero for a writer completed before the first10ms sample means NO RSS SAMPLE, not zero memory use; AS cap still applies. Parent final exits are in tool receipts, not invented in pre-exit disk logs. Early inline inspections lack per-process persisted peak/CPU samples; their commands show pre-read caps, and this limitation is not retroactively repaired. No other spawned converters or mathematical jobs exist. Actual manifest has explicit self-reference exclusions; manifest verification is separate.
