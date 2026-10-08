# H017 information mechanisms: conditional recovery and missing signals

Status: paper analysis; no verified improvement, numerical run or Lean claim.
Factory Opus's raw report is retained, including its unmeasured estimates and
admission that sources were cited from memory. Native Astra
`/root/h007_additive_relations` independently reviewed cards1/2; native Sol
`/root/h010_early_dependencies` reviewed card3 and the recurrence statement.
Root checked the arguments and consulted the primary sources below. Full
original taskId is in H017-independent-briefs.md, suffix
`ecdloop-h017-information-mechanisms-factory-opus-20261008-r1`; COMPLETED,
summary read, no pending child runs. Reviews are read-only; root integrates.

The working classical reference is square-root work, with known automorphisms
where applicable and all setup, memory, failures and verification charged. None
of these conditional bridges supplies the cheap useful public feature it needs.

## 1. Sparse scalar-field features via geometric samples

Suppose, as a GLOBAL hypothesis on nonzero scalars,
`f(nG)=sum_j c_j n^e_j` in Fq, with distinct exponents modulo q-1 and c_j≠0.
For a certified primitive w, the sequence f([w^i]G) is a sum of exponentials
with distinct bases w^e_j. Its full-period linear complexity equals the number
of terms. This makes recurrence discovery and Vandermonde recovery a valid
conditional approach, not evidence that centered coordinates have this form.

A low-order recurrence fitted to2T values does NOT certify this global
hypothesis. In particular, observing finite-prefix complexity T does not reject
global complexity≤T. It excludes only orders strictly below the observed
minimum. Fresh checks can falsify a candidate or give a quantified empirical
test; final scalar verification proves only a successful individual answer.
A nonsingular (t0+1)-square Hankel minor would be an exact certificate excluding
all global t≤t0 sparse-power representations for that feature on that instance.
No such numerical certificate was computed in this wave.

If the global form holds, target samples give d_j=c_j k^e_j. Recovering the
exponents from w^e_j requires a paid finite-field discrete-log method; factoring
q-1, finding/certifying w and factoring the recurrence also cost work. After
obtaining all k^e_j, let g=gcd(q-1,e_1,...,e_t). For g=1, a Bézout combination
recovers k. For g>1 these observations leave g possible scalars in a coset;
root extraction and candidate enumeration or a justified subgroup-action search
must be paid. Verification alone does not choose the correct root for free.

The raw condition t≤q^(1/2-ε) is insufficient for its ordinary O(t²) BM
implementation: that arithmetic term alone needs t=o(q^(1/4)) for little-o
square-root field work. Faster implementations require their own bound, plus
scalar sampling, roots/logs, Vandermonde work, bit costs and residual recovery.
A finite-field NFS heuristic is not a deterministic all-input guarantee.

The proposed four-feature, three-curve, T128 probe is a possible bounded-class
falsifier, not an exact test of all sparse structures or an asymptotic theorem.
Its one-million-event estimate has no frozen implementation ledger. Full offline
log/random tables for controls would themselves consume setup and memory;
generate planted control values from known calibration scalars instead, without
giving a solver a hidden inverse oracle. Random-prefix null probabilities need
a specified iid model and multiple-test accounting; real coordinate samples
are not automatically iid. No automatic block-Hankel expansion is admitted.

## 2. Polynomial agreement via list decoding: a corrected conditional bridge

Assume a fixed public feature f agrees with a polynomial P(n) of actual degree
d, 1≤d<q, on densityρ of all scalar inputs. Values at O and coordinate poles
must be defined. Both calibration and target decoding produce LISTS. For the
correct pair P and P_k(r)=P(k+r),

    coeff_(d-1)(P_k) = coeff_(d-1)(P) + d*coeff_d(P)*k.

The denominator is nonzero under these hypotheses. Enumerate compatible
calibration/target pairs and verify recovered scalars; charge list lengths and
verification. Constants provide no scalar information, and a vanishing
characteristic-times-degree coefficient invalidates this extraction formula.

The raw N>d/ρ² is only the indicative decoding-radius condition. The actual
sample agreement must exceed sqrt(d N) with a chosen margin, and decoder
complexity depends on its interpolation/factorization parameters. Neither a
generic cubic nor a quasi-linear whole-decoder bound is established here.

Cheap sampling can be repaired. Choose uniform a and nonzero b in Fq and
sample n_i=a+i b, 0≤i<N≤q. The positions are pairwise uniform and distinct,
though not iid. For a fixed agreement set of densityρ, the sample-average
variance is exactly

    ρ(1-ρ)*(q-N)/(N*(q-1)).

This follows by counting ordered distinct pairs: their joint membership
probability is |A|(|A|-1)/(q(q-1)). Chebyshev bounds failure to reach any fixed
margin belowρ. Thus random progressions can support a weaker, explicit
confidence guarantee while costing two scalar-multiplication starts plus
O(N) additions on each side; target points begin at Q+aG and step by bG.
Use independently chosen progression parameters for the two lists, and union
bound their failures. Consecutive deterministic sampling or merely uniform
marginals would not suffice for this argument.

This repairs an operation in the conditional solver. There remains no proposed
reason for any listed coordinate feature to have the required agreement.
The raw RANSAC counts, 64-check decision and claimed budget are not a frozen
power analysis or full-work ledger. A negative finite search would exclude
only its declared degrees, density, features, instances and confidence, not all
polynomial information. No such search was run.

## 3. Approximate orbit labels: separate the label, sampler and detector

On nonzero points of the order-q group, let K⊂Fq* have order h and define
`c=Pr_{P,u in K}[I(P)=I([u]P)]`. For independent uniform P,R the probability
of a true label collision WITH R in K*P is exactly τ=h*c/(q-1). Let
κ_total=Pr[I(P)=I(R)] and κ_false=κ_total-τ. Use κ_false, not κ_total, in
the false-candidate ledger; the raw report intends between-orbit false collisions.
Always κ_total≥τ. The singleton O requires separate full-domain terms.

For a predeclared iid batch at N²≈1/τ, false candidate count has expectation
O(κ_false/τ). Charge setup/training, sample/feature/store work, EVERY reported
candidate, orbit-membership tests, rejection and scalar verification. The
stated generic action-BSGS costs O(sqrt(h)*log(q)) additions per orbit test,
including failures; parameter/group-action certification is additional setup.
Solving a true relation requires a nonzero label coefficient. Random label
masks with coordinate-only selection can justify this, but walk/grid labels
need the actual distribution argument.

The proposed table grid R_ij=A_i+B_j is not iid. Independently uniform source
tables make distinct cells pairwise independent, preserving pair means, but
R11+R22=R12+R21 creates higher dependence. Reusing an index pair creates a known
useless collision. Charge source tables and do not import an iid hitting law.
No concrete useful I, sampler-success proof or complete-work gain is supplied.

Root repaired an initially overstrong reviewer caution about iid bucket skew;
Sol independently confirmed the following second-moment proof in a NEW focused
native followup. Partition points by the HIDDEN cell (K-orbit,I-label), with
probabilities p_j. Then τ=sum p_j² and σ3=sum p_j³≤τ^(3/2). For the number C
of matching unordered pairs among N iid samples,

    E C = choose(N,2)*τ,
    E C² = E C + 6*choose(N,3)*σ3 + 6*choose(N,4)*τ².

At N=ceil(2/sqrt(τ)), the mean is bounded below and second moment bounded above
by positive absolute constants; the second-moment inequality gives constant
success. Fresh independent blocks yield O(τ^(-1/2)) expected samples; the
union bound gives the matching Ω order. Thus arbitrary skew does not invalidate
the iid Θ birthday ORDER. The raw exact constant remains unsupported. With
independent uniform label masks conditional on points, coordinate-only selection
retains a useful denominator with probability1-1/q. Two independently labelled
copies of the same point can be useful; reusing the identical stored record is
tautological. This proves sampling order, not cheap discovery of the hidden cell:
the observable I-buckets still require paid false-candidate orbit tests.

Exact K-invariance implies exact invariance under subgroups. For approximate
invariance there is a weaker useful statement: if c≥1-ε, every fixed v∈K has
Pr[I(P)≠I([v]P)]≤2ε. Average the triangle inequality through a uniform [u]P.
Moderate consistency does not imply exact subgroup invariance; an exact μ3
kernel rejection does not reject approximate labels.

For a NONCONSTANT rational function g of degree d and an integer |u|≥2 acting
invertibly on the q-group, g∘[u]-g is nonzero (composition degrees differ),
has pole degree≤d(u²+1), and has at least q-2d zeros if values agree at all
rational group points where both are finite. Hence d≥q/(u²+3). This counts
rational-function equality, not hashes or bins. For large u the bound may be
vacuous. A function-field identity itself is impossible by degree for |u|≥2;
finite-group equality is a different claim.

Stage A's sampled evaluation matrix for
V=span{x^i y^j:0≤i≤D, j≤1} can prove a LIMITED exact negative: if its kernel
is constants only, no nonconstant exact invariant in V exists on that instance,
since the global invariant space is contained in the sampled kernel. A positive
sampled kernel plus fresh checks is only a candidate. The j0 x³ control has its
own known endomorphism proof and supplies no generic transfer. At D50, V has
dimension102 and204 proposed samples; straightforward elimination after deleting
the constant column entails about858500 multiply-subtract updates PER curve,
already above the proposed total budget for three curves before setup. A new
frozen algorithm could differ. The unspecified Stage B contrastive learner is
not admitted, whether Stage A returns positive or negative.

## Scope of the two claimed pruning facts

For p≠q, the minimal polynomial of the ENTIRE q-periodic Fp-valued sequence
f(nG) divides X^q-1. Every nonconstant part contains an irreducible factor of
the qth cyclotomic polynomial of degree ord_q(p); thus full linear complexity
is at least that order. No distribution theorem here makes it "usually q".
This statement does not prove the raw Miller/Kummer/cross-characteristic
exclusions or rule out every recurrence-based algorithm. Characteristic-q
additive-period polynomial structure and geometric-period sparse structure are
separate cases.

The pair-predictor reduction B(D)=A(R,R+D) preserves accuracy only under the
specified uniform-mask/difference distribution and paid fresh random R. It is
not a classification theorem for all learned methods. The raw dismissed routes
(point-count observables, isogeny models, representation methods and arithmetic
schedules) are not universally ruled out by these two facts.

## Primary sources actually inspected by root

[Ben-Or–Tiwari1988](https://www.cecm.sfu.ca/personal/monaganm/teaching/TopicsinCA15/BenOrTiwari.pdf),
§§1–4,6,8: the interpolation problem is given a sparsity upper bound and uses
a real/complex algebraic RAM. Its recurrence/Vandermonde mechanism motivates
the conditional construction, but does not establish coordinate-feature
sparsity or supply finite-field exponent extraction costs. The discussion of
unknown sparsity explicitly separates discovery from stopping certification.

[Guruswami–Sudan1999](https://www.site.uottawa.ca/~zhcheng/list_dec.pdf), abstract,
§I and decoding setup: distinct evaluation points and sufficient actual
agreement permit list recovery. The source emphasizes polynomial-time recovery
rather than optimized runtime. Root's Harvard author-hosted URL open failed;
the university-hosted published-paper copy was read instead. No fast full-decoder
complexity or ECDLP-specific feature agreement is imported from it.

## Ranked disposition and next decision

1. Sparse geometric recurrence: most direct bounded falsifier among these
   cards; cheap public feature is explicit, but useful sparsity is unsupported.
   Any admission must freeze a smaller exact exclusion threshold, global
   accounting and controls; the raw T128 budget/test is not accepted as written.
   Astra's completed review admits consideration of ONE frozen small-curve probe
   with at most256 shared samples and a stop at prefix complexity128, precisely
   excluding global t<128. Root accepts a paper/code preflight for that narrow
   diagnostic, not the uncosted three-curve campaign or automatic followups.
2. Polynomial agreement: corrected conditional recovery and cheap progression
   sampling survive. Park decoder implementation pending a concrete signal or
   independently justified bounded diagnostic with declared statistical power.
3. Approximate orbit label: potentially material conditional gain, but the
   label itself is absent. Require an explicit I and favorable paid
   (c,κ_false) prediction; do not run generic contrastive training.

No new numerical evidence changes H014's latest recorded result. No asymptotic
or practical gain is claimed, and none of the failures proves coordinate-aware
ECDLP impossibility. This review preserves useful recovery methods while
rejecting unproved global identities, missing work and overbroad exclusions.

Specific RANSAC warning from the independent review: atρ=.03,40000 random
triples give only1.08 expected all-inlier triples, and64 validation positions
give only1.92 expected genuine agreements. Literal validation of every proposed
candidate entails2.56M candidate-position checks before interpolation/setup.
Early abort would need its own declared power/cost analysis; the raw claimed
budget does not establish it.
