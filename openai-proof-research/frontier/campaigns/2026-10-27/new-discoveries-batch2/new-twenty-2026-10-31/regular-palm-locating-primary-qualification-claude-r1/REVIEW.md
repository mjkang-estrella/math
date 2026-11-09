# REVIEW: MathDB 344875, regular palm locating-chromatic conjecture

Independent adversarial qualification by Claude Opus 5.5 (first independent review).
Credit 0. Campaign 57/80 unchanged. Root alone adjudicates acceptance and credit.

## RECOMMENDATION: EXCLUDE AS ROUTINE OR CORRECTION

Moderate confidence; this is a judgment call that the user or root may overrule.

The mathematics is correct. I found no error and no literal defect. The exclusion rests on
what the result adds over the source's own proof, not on any flaw and not on shortness alone.
It is NOT a finding that the result is already public: no earlier proof was located.

If overruled, the only defensible unit is the all-k exact-constant theorem, never the k=4 witness.

## 1. Result reviewed

Fix k>=2, l=floor(k/2), u=ceil(k/2), beta_k=(l^l u^u)^(1/k). Then chi_L(S_n(k)) = beta_k n^(1/k) + O_k(1).
For every k>=4, beta_k < ((k-1)/2) 4^(1/k), so Conjecture 5.1 is false at every k>=4.
beta_4=2 against the printed 2.1213...

The theorem is correct. I reconstructed it before opening the author's file (PROOF.md, whose bytes
were written first; see section 10), then audited the author separately.

## 2. Separate gates

| Gate | Result | Basis |
|---|---|---|
| Literal | PASS | The record matches Conjecture 5.1 of v2 (viewed on p.10). o(1) means k fixed, n->infinity; source Corollary 4.1 rules out a uniform-in-k reading. |
| Original source | PASS | v2 read completely as text; pp.1,2,9,10,11,12 viewed as rendered pages. v1 not supplied or read. |
| Final / correction | BOUNDED, no final found | Fresh arXiv listing: v1, v2 only, no journal reference. Not proof that no final exists. |
| Ordinary proof | PASS, all k>=2 | Independent PROOF.md, plus full audit of the author (section 3). |
| Prior art | BOUNDED NONMATCH | Two searches, one string each; section 6. Not a novelty certificate. |
| Novelty | NOT CLAIMED | No worldwide claim. |
| Significance | FAIL (recommended) | Routine extension of the source count plus an optimization correction of an unproved guess; sections 4, 5. |
| Family | PASS, no overlap | All 96 supplied scopes compared; section 8. |
| Formal | NOT DISPATCHED | Section 9. No Lean run. |
| Process | PASS with disclosures | Section 11. Not a universal compliance claim. |
| Acceptance | ROOT ONLY | Credit 0. |

## 3. Audit against the author's section 8 checklist

Every item checked by hand. The author's text is correct on all of them.

1. Distance formula, depth-D_t vertex on the same arm. Correct. If the only depth-D_t vertex of colour t is on arm i,
   then 1+D_t overstates the off-arm term, but that arm's own term D_t-1 is smaller, so the minimum stands.
   My PROOF.md section 2 splits the same cases: "else" can only happen when a level-D_t vertex lies on another arm.
   Hub colour: D_h=0 gives value 1, which is the hub. Position 1 is excluded by properness, and positions j>=2 give j-1>=1.
2. Strict inequality. Correct. For q in {s,s+1} and D_t>=s we have q<=D_t+1, so |j-q|<=j+q-2<=j+D_t-1<j+D_t for j,q>=1.
   The worst case q=s+1, D_t=s is covered.
3. Sum bounds. Correct in both parities: odd factors sum to at most m+u-1 (=m+l when k is odd, m+l-1 when k is even), even factors to at most m+l.
4. Proper colouring and nonempty classes. Source p.1 says only "k-coloring", but the source's proofs use properness (p.5, p.11).
   The result does not depend on this: my lower bound holds for arbitrary colourings (a +1 at position 1), and the construction is proper and surjective.
   Empty classes only lower the sum of the a_s.
5. Coverage and range of n. Correct. Tuple extension works with a_1>=2 and a_{j-1}+a_j>=2, and needs n>=M=O(n^(1/k)), so n>=n_0(k).
   Profile arithmetic rechecked: r(r+1)y = beta_k n^(1/k) and |A|>=n.
6. Meaning of (1+o(1)). k fixed, n->infinity. Confirmed from source p.9.

Also checked: the corollary (both parities; the sequence (1-1/x)^x increases), the worked k=4, b=2 codes, and the printed-constant calculation in section 5 of the author file.

The two constructions differ harmlessly. The author reserves h for the hub, so one coordinate reads the level. Mine reuses h and reads the level from a colour absent from the arm.

## 4. The five adversarial questions

### Q1. Is the all-k result a routine extension of the source's k=2 and k=3 arguments?

Yes for the lower bound. For the construction it is a routine variation, not a verbatim index change.

Source k=3 count (p.11). With A,B,C the colours at hub distance 1,2,3, the source writes
a_p=1, a_j=2 for j in A\{c(x_i),c(y_i)}, a_j=3 for j in B\{c(y_i),c(z_i)}, a_j=4 for j in C\{c(z_i)}, and says the code of x_i "depends only on c(x_i), c(y_i), and c(z_i)".
Four cases total alpha(alpha+beta)(beta+gamma)+alpha^2, then p.12: "maximized by taking gamma=0", then one-variable calculus gives alpha near p/2.

Source k=3 construction (p.12). A has ceil(k/2) colours, B the rest of k-1. S_1..S_4 are tuples (a,b,a), (a,b,c) with b,c in B, and (a,b,a), (a,b,c) with a,b in A u {k}.
So B already sits at the adjacent positions 2,3 and A at positions 1,2, with an inert repeat of a at position 3. The proof splits on the parity of the distance to the hub colour.

Source general-k construction (p.10, Theorem 5.1). One colour class per position, full product, "It is easy to verify".

Bridge for the lower bound. Replace A,B,C by W_1..W_k. The p.11 display becomes a_j=s+1 for j in W_s minus the colours at positions s, s+1: the same statement with s in place of 1,2,3.
What must be added is only (i) replacing the four-case total by the crude product w_1 prod(w_{j-1}+w_j+1), and (ii) AM-GM on the disjoint odd and even chains in place of the p.12 calculus.
That is the complete proof. It is the source's count with a change of index plus a two-line inequality.

Bridge for the construction. Take the Theorem 5.1 per-position classes and allow position j to use L_{j-1} u L_j, which is the adjacent-position pattern the source's S_2 and S_4 already use.
What must be added is a general decoding argument, because the source's parity split is specific to k=3. That argument is about ten lines (absent colours give p+j, present colours give |p-j| or |p-j-1|, and these differ). It is simpler than the source's, since only the leading order is needed.

Honest limit: the source does not contain the general decoding step or the two-chain inequality. Those are reviewer- or author-supplied bridges, and I do not claim the source states them.

### Q2. Is the refutation only an optimization correction of an unproved guess?

Largely yes. Setting om_1=...=om_{k-1}=1/(k-1), om_k=0 in om_1 prod(om_{j-1}+om_j) gives (1/4)(2/(k-1))^k, which is exactly q=((k-1)/2)(4n)^(1/k).
I derived this independently (PROOF.md section 8) and it matches the author's reconstruction. So the printed constant is the uniform allocation over levels 1..k-1. It is the true optimum at k=2,3 and suboptimal for k>=4.
The source gives no reason for it: p.10 says only "We end this section with the following conjecture." The uniform-allocation origin is therefore a reconstruction, not something the authors state.

Two units of credit:
- k=4 witness: ordinary coefficient tuning. Two equal colour blocks at levels 1,3 beat the uniform allocation. Only the construction is needed. Comparable to the two-term family the user declined at 323531. Zero.
- All-k exact-constant theorem: more than tuning, because it has a matching lower bound and a closed form for every k. But the lower bound is the source count re-indexed and the optimum is elementary. It does not, in my judgment, rise above a routine extension under campaign policy.

### Q3. Is it known or implied?

Not found, within a small bounded search (section 6). No applicable theorem was read. A bounded nonmatch is not a worldwide novelty claim.

### Q4. Is there a shorter generic argument?

Not a shorter one. The proof is already the generic route. The window lemma is the triangle-inequality trichotomy behind source Theorem 3.1 (p.5, neighbour coordinates lie in {a-1,a,a+1}), plus the fact that an arm holds one colour per position.
I found no general theorem on locating codes or partition dimension of bounded-depth trees that implies the constant. Metric dimension does not help: it is about n-1 here and carries no colour-class information.

### Q5. Family comparison

See section 8. No locating or metric-dimension overlap.

## 5. Strongest case on each side

For credit:
1. A deliberate printed conjecture is false at every k>=4. This is a real refutation, not a wording, domain or endpoint repair.
2. It settles the leading constant for every k with O_k(1) error, where the source had only Theta(n^(1/k)) with constants 1 and 2k and exact results for k<=3.
3. The answer has a matching lower bound, and the optimum has an alternating zero pattern that k<=3 could not reveal.
4. The source's k=3 locating proof does not generalize verbatim, and no earlier proof was found.

Against credit:
1. The lower bound is the p.11 display with a change of index, plus two lines of AM-GM. There is no new invariant.
2. The construction combines patterns the source already uses (Theorem 5.1 per-position classes; S_2, S_4 adjacent positions), with a short decode.
3. The printed constant is exactly the uniform guess. The refutation optimizes the same functional the source's count produces.
4. k=4 alone needs no lower bound and is two-block tuning.
5. Nothing in the source or the search suggests difficulty, unlike 382297, where a journal paper called the problem unexpectedly difficult.
6. Same pattern as prior exclusions 352895 and 350767: a source step is extended or one estimate replaced, with the source's own architecture intact.

Bias disclosure: TASK disclosed the mechanism and the value of beta_k before I began, so the ease of my reconstruction overstates how easy the discovery was. I did not count ease as evidence. The argument above is about the source-to-target bridge.

## 6. What the bounded search did and did not cover

Performed: 2 native searches, 1 string each (budget 2 calls, 6 strings); 5 of 6 GET hops; no redirects.
- arXiv listing, fresh: v1 (12 Dec 2019), v2 (17 Nov 2020), no journal reference.
- Amrullah, Partition dimension for a subdivision of a homogeneous firecracker, EJGTA 8(2) 2020: first pages and keyword scan only. Firecrackers; no spiders or asymptotics. Nonmatch.
- Khali, Husain, Nadeem, AIMS Math 7(3) 2022: first pages and keyword scan only. Convex polytopes. Nonmatch.
- Hasibuan, Abidin, J. Mat. UNAND 14(3) 2025: first pages and keyword scan only. Complete and complete bipartite subdivisions of at most three edges. Nonmatch.

Not covered or closed:
- IAENG IJAM 54(10) paper 09 (https://iaeng.org/IJAM/issues_v54/issue_10/IJAM_54_10_09.pdf): TLS certificate failure before any body; title unknown; closed, no retry or bypass. Treated as work-specific closure, not as evidence for or against.
- Amrullah et al., The partition dimension of subdivision graph on the star, J. Phys. Conf. Ser. 1280 (2019) 022037: unread, seen only as a reference in the AIMS paper. Not requested: an IOP DOI chain would need more hops than the single remaining one, and a recorded IOP chain reached a verification page. The title suggests subdivision of a star, and it concerns the improper invariant, so it could be relevant; applicability is unknown. I do not treat it as an applicable-prior HOLD, because nothing identifies a matching theorem, but root should know it is unread.
- Not searched: citation indexes (Google Scholar, MR, zbMATH), theses, non-English literature, later Hafidh or Baskoro papers beyond what the two strings returned.

## 7. Source reading inventory

Text read completely: inputs/sources/1912.05775.txt (40776 characters, ranges 0-15000, 15000-30000, 30000-40776).
Viewed as rendered PNG: pp.1, 2, 9, 10, 11, 12. Glyphs checked: definitions, the Conjecture 5.1 constant, Theorems 5.1-5.3 and their proofs. Pages 3-8, 13 read as text only.
TASK.txt read 0-13449. inherited-denials.json read completely in 20 contiguous chunks, 0-297884.
Search responses saved in the next tool call after each search returned.

## 8. Family comparison

All 39 prior scopes (id, title, scope field) and all 57 accepted records read.
55 accepted records carry a statement field; 2 (324571, 326555) carry a scope field instead, and those were read.
Nearest neighbours by topic only: 339235, 354228, 365453 (local antimagic chromatic numbers); 350979 (monophonic position); 346167, 355140, 355217, 360905 (other graph parameters); prior #36, #38 (Steiner tensor on a star, edge irregulator).
None concerns locating colourings, partition dimension or metric dimension. No family overlap.
The trusted scopes were used as routing data; no accepted certificate was opened.

## 9. Formal

No Lean was run and no formal plan is authored, since the significance gate fails on my recommendation.

Is the k=4 endpoint the right literal target? Yes. The printed claim is universal in k>=4, so its negation needs one k, and "not Tendsto ... (nhds 1)" at k=4 is the exact negation of (1+o(1)) at that k.
It needs only the upper bound along n=(b(b-1))^2, which is robust: any broader definition of colouring can only lower chi_L, and the witness is proper and surjective, so it satisfies the narrower one too.
If dispatched, a definition must not quietly collapse: sInf of an empty set is 0 in Lean, harmless along this subsequence but worth a fidelity note.

What the all-k theorem would add: the general window lemma and pigeonhole, the two-chain AM-GM, both parity profiles and coverage for general n, and the corollary for every k>=4. Credit, if any, should attach only to that statement; the k=4 endpoint alone pays the literal negation but not the unit worth crediting.

## 10. Order of work

PROOF.md was written before inputs/author-FULLCANDIDATE.md and inputs/author-DORMANT-FORMAL-PLAN.md were opened; the receipts show write and read order (read_author.receipt.json follows PROOF.md's creation).

## 11. Process disclosures

- Five failed receipts, scopes_acc_a through scopes_acc_e, exit 1: a KeyError on 'tags' in my own display script, sent as one parallel batch before I saw the first result. No data was affected. Retained. Repaired with a changed script as scopes_acc_r1 to r3.
- One failed GET, get_1, true exit 1: TLS verification failure. Retained. No retry.
- Denial and TASK chunks were issued in contiguous parallel batches. Each was at most 15000 characters and all ranges are recorded.
- One shell command used `cd` into the lane before the runner; no effect on the helpers or outputs.
- PDFs of the three bounded nonmatches were read only on their first pages and by keyword scan, as stated.
- Native, transient, writer and supervisor resource peaks are unknown. No universal cap-compliance claim is made.
- No Lean, program, enumeration, CAS, solver, child agent, git or external message was used.
