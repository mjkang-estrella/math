# TREE097 independent full-scope proof review, round 1

Reviewer: independent proof-review sub-agent (no author role, no nested
agents, no uploads). Original review prose CC BY 4.0; code MIT.

Target packet (read-only, unchanged):
frontier/campaigns/2026-10-14/fresh-structural-discovery-r44/

| file | SHA256 (recomputed, equals brief anchor) |
|---|---|
| MANIFEST.json | ceb4d164b90d6ed3c81ba0338e120b5ee641cf7a46e9f2a18b8e7fa2c25e572e |
| candidate.md | 7035c4b5216ac37610132045608041110722980c6546746491803e52c21889a8 |
| original-scope.txt | 08338d40a730c126691accaaa60db530116b5df44393ca22d2c1663cc9099821 |
| prefix-law.md | baa4071a53f0c80e8af9be3f8179e877220497317cd2f24c73f7ee74ab1ac8ee |

## Verdict

**PASS_FULL_TREE097.**

The candidate proves the unchanged frozen statement of original-scope.txt at
its full quantifiers, conditional only on (i) the pinned source097 statements
(stipulated true) and (ii) the published primary theorems DGLN2019 Thm 1.2 /
Thm 3.4 and Bansal–Jiang–Meka–Singla–Sinha 2111.07049v1 Lemma 4.1, each used
inside its actual stated hypotheses. Every new deduction listed in the brief
was rederived independently (rederivation.md). No required objection is
mathematically blocking. This verdict concerns proof correctness only. It
is not a contribution, eligibility, novelty, or formal-verification verdict,
and it changes no campaign count (13/20 unchanged).

## Exact frozen-scope coverage

| frozen quantifier / clause | where established | status |
|---|---|---|
| one absolute C | constants A,s (prefix law), B=sqrt8 s, A_0' (source097), C_0=5 (Bansal), all absolute; explicit regime constants in rederivation.md §9 | covered |
| every d>=1 | prefix law needs d>=1 (prop:filtered); unary regime d>=2 via Bansal, d=1 by greedy | covered |
| every finite nonempty rooted tree, any degrees | heavy-light and unary partitions exist for every finite rooted tree; counts use only L | covered |
| L = number of leaves, bound C sqrt(d log(1+L)) | §7 regime split q<=d / q>=d, q=log(1+L)>=log 2 | covered |
| unit-ball labels, zeros, repetitions | all inputs are unit-ball statements; b_i=0 handled (eta=1/2, C=I) | covered |
| ONE signing for every root-to-vertex sum, both endpoints | heavy-light: realization in positive-probability event; unary: one flip per chain times one chain signing | covered |
| independent of N, depth, unary lengths, degrees | hard prefix bound is length-free; union bound has L*5^d terms; unary compression has m<=2L-1 nodes | covered |
| empty tree / d=0 trivial | stated explicitly | covered |
| existential, offline; no algorithm/sharpness claim | no such claim made | consistent |
| r4 two-order target unchanged, not restricted | original-scope.txt and candidate §8 | consistent |

No weakening was found: the proof does not reduce to terminal marginals
(internal prefixes are used, §5), does not use one marginal-specific law per
prefix (one law per whole chain), does not assume bounded depth or large d,
and does not use a vertex-count union bound.

## Required objections

None of these is a mathematical gap; each must nevertheless be corrected in
any manuscript or acceptance record because the present text is inaccurate
or incomplete as written.

R1. Candidate §2 / prefix-law §2 ("Gaussian body"): "Every unit-direction
support WIDTH of K is at least a" should read "the support function
h_K(theta) is at least a for every unit theta". Width is 2h_K. A width bound
of a would only give (a/2)B_2 in K, and then K+aB_2 is not shown to lie in
2K. The slab argument actually written (K inside a centered slab of measure
<1/3) does prove h_K>=a, so the proof is correct, but the sentence is wrong.
Also "a B_2 contained in K" should be "aB_2 contained in K".

R2. Candidate §3: the identity x=x(epsilon) needs the fact that the source
prop:adaptive starts from x^(0)=0 and changes only the listed coordinates, so
the initial d-block of the output stays zero. This is in the actual source
statement (assembly.tex lines 39-49; and lines 209-221 of the source's own
use), and without it R_0x=0 and the exact cancellation would fail. The
candidate uses it implicitly ("Since R_0x=0"); it should be stated.

R3. Candidate §4: the DGLN conversion should state the homogeneity step and
the body convention explicitly. DGLN line 605 defines a convex body as closed
with nonempty interior, not necessarily bounded. A_good meets (3D_G)B for
every such symmetric B with gamma(B)>=1/2, so s_b(A_good)<=3D_G, and DGLN
Thm 3.4(2) gives s_g<=sqrt2*3D_G. The candidate's prose ("c_0 absolute") is
correct but leaves this to the reader.

## Optional objections

O1. Bansal et al. Lemma 4.1 is stated for "any convex body", but its proof
uses Banaszczyk's Lemma 2.5 (symmetric bodies) and a root step that needs a
centered ball inside K_r. The candidate correctly applies it only to a
centered Euclidean ball, and its §6 sentence on the root step supplies the
missing ball. It could add that only the symmetric case is used.

O2. Candidate §5: the bound "at most K ancestor chains" follows because the
chains met strictly before C on the root-to-head path are in bijection with
the light edges on that path (one new chain per light edge; the root chain
pairs with the light edge into the first non-root chain). Stating this
one-line count would help.

O3. Candidate §2: the closing sentence on open and unbounded bodies is more
general than needed. For DGLN only closed (possibly unbounded) bodies occur,
and truncation by a large closed ball suffices. The extra open-body clause is
harmless.

O4. The candidate's MGF constant (B=sqrt8 s) is valid. The copied analytic
note derives B=2s via (2k)!>=2^k(k!)^2. Either suffices; the record could
use one.

O5. Candidate §6 writes C_0 for the Bansal constant; the read proof gives 5
after scaling labels by 1/5 (Lemma 2.5 needs norm <=1/5). Recording the value
is optional.

O6. Candidate §8 and history-and-comparison.md mix proof and contribution
claims ("the candidate deduction is ..."). Those claims are outside this
gate and were not used as evidence here.

## What was checked, in brief

Full details are in rederivation.md. All of the following were
independently rederived and found correct:

1. Intersection energy lemma via closed-set Gaussian path correlation,
   open-set survival rates, and a -> 1 (no closed/open rate equality used).
2. Gaussian-body energy bound H_G=6/a^2+3/2 with the source normalization
   (no 1/2 factor in lambda_Q), including H^1_0 membership of the test
   function and dimension independence.
3. Reserved slack: lambda_Q(K_0)<=kappa^2 trQ/2 from the source slab lemma
   and column bound; lambda_Q(K_0 cap E)<=kappa^2 trQ.
4. A_good is a fixed finite symmetric set, defined before any auxiliary body.
5. Causal clipping and unclipping, with the output's zero initial block, give
   x=x(epsilon) in A_good and in 3D_G B.
6. Exact cancellation R_i x = sigma * prefix_i, and R_i R_i^T = I_d.
7. Correct DGLN finite-set law (actual statement and operative proof read),
   symmetrization, injectivity epsilon <-> x(epsilon).
8. Simultaneous hard support for all prefixes together with subgaussian tails
   for every fixed prefix, from one law.
9. Symmetric-tail to MGF conversion.
10. Heavy-light: L chains, at most floor(log2 L) light edges, fixed internal
    prefixes of distinct independent chains, Chernoff, a net of size 5^d,
    union over exactly L*5^d pairs, positive-probability realization.
11. Unary compression: m=L+b<=2L-1, exits only at endpoints, whole-chain flips
    keep hard bounds, Bansal Lemma 4.1 hypotheses met by a Euclidean ball of
    Gaussian measure >= 1-1/(2m), d=1 greedy.
12. Both regimes, L=1, d=1, zero and repeated labels, empty tree, d=0.

## Integrity checks performed

- Author verify.py inspected (read-only, requires caller anchor, rejects
  links/hardlinks/nonregular nodes) and run: PASS with the brief anchor
  (90 payload files, 25 directories, 51 pinned blobs, 8 primary pairs);
  FAIL with a wrong anchor.
- All 51 source bodies recomputed as Git blob SHA1 and compared against the
  complete sources/preprints-tree.json (SHA256
  eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b,
  truncated=false, 13223 entries): 51/51 match.
- The 7 primaries relevant to this proof were re-downloaded from their
  recorded URLs to /var/tmp: bytes and SHA256 match receipts, and
  pdftotext -layout (poppler 26.01.0) reproduces the recorded text SHA256.
  Dvorak–Yepremyan (unrelated 157/184 screen) was not re-downloaded.
- These identity checks certify file identity only, not mathematics.

## Supplementary finite diagnostic

checks/reviewer_diagnostic.py (exact rationals) checks the filter algebra on
184 sign patterns (C^2+bb^T=I, R_iR_i^T=I, causality, column bound,
cancellation, injectivity, oddness, including zero and repeated labels) and
heavy-light / unary identities on 400 random rooted trees (up to 40 vertices,
long unary stretches, high root degree). Mutating heavy-child choice or eta
makes it fail. It is not proof evidence for the universal theorem.
