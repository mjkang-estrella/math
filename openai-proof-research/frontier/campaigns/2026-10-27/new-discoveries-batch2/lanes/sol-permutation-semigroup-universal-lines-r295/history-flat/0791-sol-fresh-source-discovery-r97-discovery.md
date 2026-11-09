# r97: full ordinary Chatterjee triangle refutation; qualification HOLD

Research date 2026-10-29 UTC. Solo; writes restricted to this lane. Counts remain
8 additional / 38 total. No Lean, paper, public action or acceptance is proposed.

## Exact source questions screened

1. **Selected:** Flavio Chierichetti, Mirko Giacchini and Ravi Kumar, *On the
Metricity of the Chatterjee Correlation Coefficient*, author-hosted accepted
manuscript dated 2026-02-21, Section6, PDFpp17–18. The footnote identifies the
published article DOI10.1080/00031305.2025.2571183, published online19Nov2025.
The actual body leaves open whether d, d'_avg and d'_min obey an approximate
triangle inequality. Equations in Sections1 and4 fix all three definitions.
The full uniform multiplicative version is: for each distance D, does there
exist a finite K>0 such that for EVERY jointly distributed nonconstant real
A,B,C, D(A,C)<=K(D(A,B)+D(B,C))? The proof in PROOF.md answers NO for all
three, even with a joint density, uniform marginals, and positive pair distances.
The source does not explicitly choose multiplicative versus additive
approximation; this ambiguity is retained. No optimal additive constant for
d'_avg is claimed. The manuscript is at
https://mirkogiacchini.github.io/papers/cgk25_chatterjee_metricity.pdf .

2. **Fresh screened, not pursued:** Károly Bezdek, *Volumetric bounds for
intersections of congruent balls*, latest observed arXiv1912.05118, Conjecture5
(8): for every r>r0>0, N>1, integers d>k>0 and finite P of N points in R^d
with circumradius r0, Vk(P^r)<=Vk(L_(r,r-r0,d)). Here P^r is the intersection
of radius-r balls at P and L is the corresponding lens. The actual source
Theorem1 proves k=d; Theorem4 gives a weaker lens bound. Latest observed
Drach–Tatarko2511.11901v1 TheoremA proves mean width k=1, and TheoremC proves
all intrinsic volumes under Definition5.1 inball symmetry. Its proof
Section5 uses transitivity of contact points to compare mixed-volume ratios
(Lemma5.2); omitting symmetry would be an unproved extension. The survey
2411.10302, actual Theorem3.11/Conjecture3.12, records surface-area clearance
and the residual lower intrinsic-volume question. Full arbitrary P, all d,k
is not proved here; no symmetry-restricted theorem is nominated. This target
was less tractable than the explicit probability construction. Sources:
https://arxiv.org/abs/1912.05118 , https://arxiv.org/abs/2511.11901 ,
https://arxiv.org/abs/2411.10302 .

3. **Duplicate, immediately excluded:** Valmir Krasniqi2609.28707v1
Conjecture23: every interior boundary -1<b<0 has a unique positive contact,
and it is quadratic. Early local screen found sol-fresh-analysis-discovery-r5,
which already read the public resolution. Fresh actual Omega body
`docs/develop/theory/KrasniqiBoundaryContact.md` Theorem3.1 states exactly
that full result. No rediscovery investment or credit. The source's distinct
endpoint question remains r5's investigated family and is not reopened.

## Duplicate and current-public evidence

Before investment, context.py read every regular file under openai-proof-research
whose basename contains SUMMARY/discovery/FINDINGS/PROOF/review/ledger,
case-insensitively, across ALL campaign dates and output/review directories,
excluding this lane. The 7,197-file inventory has byte lengths and SHA256 hashes;
172 broad name/phrase hits are retained without using a hit cap to select them.
Chatterjee alone is broad and hits unrelated authors' research. No exact CGK
metricity report was identified in this bounded lexical screen; this is NOT a
semantic absence or priority certificate. Krasniqi was a genuine duplicate.

Fresh default HEAD responses obtained19:32UTC:

* Omega28414a3d55d5b97458b138701407d5678e167a8e,
  committer time2026-10-29T19:26:36Z.
* OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,
  committer time2026-10-26T21:18:03Z, unchanged.

Comparison from r95's a5a8bcdf56019e58c398f6f6d27a3620b896d001 returns7
commits/3 changed files. All three current changed Markdown bodies were fetched
at the immutable fresh head. They concern Auric logarithm/quantum geometry,
incidence moments/capacity, and stopped-mean spatial risk; their inspected
statements do not give the CGK inequalities. This incremental comparison does
NOT repair incomplete semantic coverage between the complete root-edge-irregulator-
final-freeze-r1 baseline and the inherited later deltas (d2b0ee6 then r95's
a5a8bcdf). The complete baseline tree filenames were searched for authors,
metricity, correlation/dependence clustering, inradius, and ball intrinsic
volumes. Relevant Krasniqi primary body and catalogue record were read. The
filename screen cannot certify semantically equivalent results under other
names. **Current semantic coverage and priority remain HOLD.** Neither
Blueprint nor Lean filenames are substituted for actual proof bodies.

## Closest classical and successor bodies actually compared

* CGK actual Lemma1/Theorems2–3: unbounded violation for d'=1-max(xi,reverse),
  a DIFFERENT distance from d'_min. Lemma5/Theorems6–7 give a fixed-factor
  violation (about0.919 in the source direction) for all three selected
  distances, without an unbounded-ratio family. Theorem8 assumes the
  aggregator vanishes on BOTH coordinate axes, which max and average do not.
  It therefore does not cover the selected symmetric functions.
* Chatterjee1909.10140v4, actual Theorem1.1 and following remarks: full
  population variance definition, independence/function characterization,
  no atom restrictions. We use the definition, not its difficult estimator
  convergence theorem.
* Fuchs–Wang2312.16544v1, actual equations(2.6)–(2.7), Example2.5,
  Theorem2.7, Corollaries3.1–3.2: predictive dissimilarities and invariance
  under increasing transformations. Example2.5's modulo map has one perfect
  directed coefficient and one tending to zero. It is a serious classical
  overlap lead. It is a two-variable statement, not a displayed simultaneous
  three-variable approximate-triangle theorem. A short adaptation may still
  suffice; no substantive PASS is inferred from the absent displayed theorem.
* Bücher–Dette2410.11418v1, actual Theorem2.1, Corollary2.2,
  Proposition2.3 and their shuffle-of-Min construction: perfect-dependence
  copulas approximate independence weakly. It concerns weak continuity;
  weak convergence alone cannot transport xi. The explicit construction in
  PROOF.md avoids that invalid transport, but uses the same coarse/fine
  information geometry. This is another substantive-overlap objection.
* Latest Ansari–Fuchs2503.11390v2 (12Apr2026), Example1.1, Lemma2.1,
  Theorem2.2 and continuity discussion: conditional-copy representation and
  conditional convergence criteria, distinguishing them from invalid weak
  continuity. No general metricity theorem was identified in those sections.

The author publications page was retrieved and matches the accepted source.
Publisher full-text request returned403 once; it was not retried or bypassed.
Thus the final published question/body comparison is **HOLD**. Search queries
combined Chatterjee with approximate triangle, metricity, shuffle, counterexample,
and the CGK authors, and separately Fuchs/Wang clustering and Bezdek intrinsic
volumes. Indexed search supplied leads, never a proof or exhaustive census.

## Sustained proof and exact adversarial validation

Take independent uniform bin indices I,J in {0,...,n-1} and independent
U,V,W uniform(0,1). Set A=(I+U)/n, B=(nI+J+V)/n²,
C=(nJ+I+W)/n². The joint density is n³ on n² disjoint boxes. With r=1/n,
the six distances are r,r,r²,r²,1-r²+r³,r, in the order AB,BA,BC,CB,AC,CA.
The directed/max triangle ratio is (1-r²+r³)/(r+r²); the average ratio is
(1+r-r²+r³)/(2(r+r²)). Both exceed n/4 for EVERY n>=2, proving the
universal failure by n>4K. PROOF.md supplies the full population integral
argument and all original hypotheses, not just checks or an isolated witness.

The first direct checker falsified my draft normalization (1/m² instead of
1/m). The corrected ratios grow linearly, not quadratically. progress.md
preserves the error and correction. Final check.py reconstructs conditional
CDFs and integrates their squares exactly over rational breakpoints for
n=2,...,12; it separately computes conditional-copy absolute differences.
66 directed distance values,33 independent copy comparisons,22 ratio bounds,
11 density normalizations and3 symbolic identities pass. The finite evidence
is only a falsifier of errors; the proof establishes every n and every K.
Use `bash run.sh`. The required unchanged helper guard enforces address space
and sampled process-group RSS512MiB, CPU210s, wall230s, nominal40ms sampling,
BLAS1. No resource caps were raised.

## Strongest objection, falsifier, and precise remaining gap

**Strongest objection:** this may be a routine adaptation of classical
shuffle-of-Min/modulo examples, despite answering the explicit source's open
question. Three-variable bin sharing plus direct definition integration is
short; absence of a printed exact counterpart does not settle substantive
eligibility. This lane makes NO new-to-literature or campaign-credit claim.

**Concrete falsifier:** any independent integration contradicting one of the
six displayed population distances invalidates the result. Orientation matters:
the target is the second variable, and source d'_min is MAX of directed
distances. The final checker tests both pitfalls and uses no rank estimator.
Adding an undocumented Markov-chain or common conditional-distribution
restriction would change the source question; none appears in Section6.

**Precise gaps:** ordinary proof has no claimed residual mathematical lemma;
independent mathematical review remains required. Source final-edition
comparison, broader closest classical-body/subsumption review, and current
semantic registry coverage remain HOLD. The unformalized adjective
'approximate' requires the parent to assess attribution to the explicit
all-K multiplicative statement; this is not permission to count a wording
repair. Optimal average additive defect and the full Bezdek conjecture are
unresolved here. No Lean/paper investment is recommended before qualification.
