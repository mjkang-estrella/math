# REVIEW: independent adversarial qualification of MathDB 353552
Claude Opus 5.5, high effort. Reviewer only: root alone adjudicates. Credit 0; campaign 58/80 unchanged. No Lean, program, CAS, enumeration or child agent.

## Recommendation: CREDITABLE SUBJECT TO LEAN AND PAPER (low-to-moderate confidence, modest significance)
I tried to exclude it and could not, on any of: a published proof, a general theorem, or a parameter-instance law.
The one surviving objection is that it is a routine refinement of the follow-up paper. That objection is a judgment
call, it is stronger than the author recorded, and root could reasonably decide it the other way on the 350767
precedent.

## Gates
| Gate | Result |
|---|---|
| Literal | PASS. tau(K_{2,l}) = Theta(sqrt l); the raw record and literal agree. |
| Original source | PASS. 2202.03431v2 read in full; definition of tau, Theorem 4, Conjecture 5 viewed as glyphs (pp2-3). |
| Final/correction | PARTIAL. Involve 16(5) 2023 final of the follow-up fetched: Conjecture 4 and the "novel refinement" sentence are retained. The journal final of 2202.03431 was not found or read; search 2 did not confirm a venue. |
| Ordinary proof | PASS. Independent reconstruction in PROOF.md written before opening the author file; author proof then audited line by line, no error. |
| Prior art | No proof found in a bounded search. Not a worldwide clearance. |
| Novelty | Bounded only. |
| Significance | Contested; see below. |
| Family | PASS. No overlap in 57+39 supplied scopes. |
| Formal | UNPAID. Dormant plan assessed below. No dispatch. |
| Process | See inventory; one disclosure below. |
| Acceptance | Root only. |

## Q1. Literal
tau(G) is the smallest k >= chi(G) with P_l(G,m) = P(G,m) for EVERY m >= k (source p2, viewed). The hypothesis
2l <= (m-1)^2 is monotone in m, so it holds for all m >= k0 = max(4, ceil(1+sqrt(2l))), and k0 >= 2 = chi. The upper bound
is paid including the "every larger m" clause. Source Theorem 4 (p3, viewed): for l >= 16, tau > floor((q/ln(16/7))^{1/2}+1),
q = floor(l/4), which is Omega(sqrt l). Its proof (Lemmas 8-12) was read and key steps checked, not line-audited. A
literal Lean endpoint must reprove it.

## Mathematics
Theorem (m >= 4, 2l <= (m-1)^2): every m-assignment has at least P(K_{2,l},m) colourings. Verified twice by different routes.
- Mine: no reduction to lists inside A cup B; per-list geometric means G_j = q^{xy} s^{(1-x)(1-y)}; reduction of all k >= 2 to
  k = 2 via B(Z) >= s^l; scalar inequality (III) in two regimes.
- Author: uses R1 (Lemma 5), exact weights q^{s_a+s_b} r^{c_ab}, averaged F <= n/4, extra mixed terms it then drops, H >= 0.
  Checked: (E1),(E2), p = 0, p = 1, (5.1), mixed and I-pairs, the collection identity, uδ >= 1, both H regimes, and Theorem 3 in
  both directions, including its use of source Lemma 12 with eps -> 0.
The sharp limit tau/sqrt(l) -> 1/(2 sqrt(ln 2)) holds. The literal needs only a constant.

Author errata. Section 7 item 2 says the joint-miss averaging (5.1) is "in nothing I read". Section 8 discloses that characters
25431-43419 of the follow-up, which contain Lemma 12 and Lemma 13, were only pattern-scanned. On the printed record (5.1) at p = 2
IS the fourth term of Lemma 13, and the block count for general p IS Lemma 12(5). The sentence is true of what the author read and
misleading about the source.

## Q2. Is the new part a routine refinement? State exactly what is new.
Already printed in 2207.04831:
- Lemma 5: lists inside A cup B.
- Lemma 6: the case k = 1, with exactly the Bernoulli compensation between diagonal gain and A'xB' loss.
- Lemma 12(1),(5): block counts for arbitrary d.
- Lemma 13: for k = 2 and every m, block-wise AM-GM on E, F, H and J = BxC. Its J term 4[(m-2)^{a2+2a3+4a4}(m-1)^{4a1+2a2+2a3}m^{a2}]^{1/4} already shows the second-order loss (m-2)m/(m-1)^2.
- Appendix A: the same blocks for m = 4, 5 and smaller d, closed by a computer check for n <= 24 and n <= 43.
Not printed:
1. Block AM-GM on A'xB' combined with diagonal Bernoulli for all d and all m.
2. The trade-off between misses of shared colours and the A'xB' block, uniformly (Delta >= kZ, or the author's x = at). The paper handles this by list types and machine checks at m <= 5.
3. The uniform joint-miss bound a_i b_i <= (p-e_i)^2/4 <= p(p-e_i)/4.
4. The reduction of every k >= 2 to k = 2. The paper only says it suspects m-2 shared colours is the barrier (p8).
5. The scalar inequality, about half a page, valid to l = Theta(m^2), and to the sharp constant.
No new invariant or construction appears. It is the architecture of the proof of Theorem 7 with its finite computer check replaced by a uniform analytic one. It is NOT Theorem 9 with a changed estimate: Theorem 9 applies AM-GM once over all m^2 pairs, which has a first-order loss: Lemma 15 needs n = O(m log m), and Theorem 9 gives only a linear bound on tau.

## Q3. Parameter instance? No.
OBSTRUCTION-K3L.md: for K_{3,l} an explicit assignment with lists D+{1,2}, D+{2,3}, D+{3,1} gives tau(K_{3,l}) = Omega(l/log l). So s = 2 is not a case of a uniform sqrt law, and the same scheme fails at s = 3 at the first step. This note is mine and has not been independently reviewed.

## Q4. General theorems? None reduces the target.
Thomassen |V|^10+1, Wang-Qian-Yan (|E|-1)/ln(1+sqrt 2)+1 and Dong-Zhang |E|-1 are linear or worse for K_{2,l}, at statement level (Dong-Zhang's body unread). The K_{3,l} note shows a bound in |E| alone cannot give sqrt. 2607.16810 was read in full: it concerns unlabeled list colourings of disconnected graphs and has no bearing. 2505.05662 (enumerative chromatic-choosability, chi = 2 characterisation; Theta(2,2,2k)) and 2605.10861 (three-path theta graphs) were read in their introductions and scanned; neither touches K_{2,l} for large l.

## Q5. Search
Two searches, two strings (budget allowed 2/6). Neither found a proof or disproof of the conjecture. Not covered: MathSciNet, zbMATH, citation indices, the journal final of 2202.03431, Dong-Zhang's body, Wang-Qian-Yan's and Thomassen's bodies.

## Family
All 96 records loaded; 57 statements and 39 titles and scope fields read (long fields displayed truncated), plus a full-text keyword sweep for list colouring, chromatic polynomial, choosability and K_{2 / K_{s. Only topical hit: 353203 (power domination reconfiguration of K_{s,t}), unrelated. 353552 absent. Theorem 1, the limit and the K_{3,l} note would be one family at most.

## Strongest case FOR credit
- A deliberate conjecture, stated in two papers, is settled in full; the published Involve text says its methods fall short and that a novel refinement or new approach seems needed.
- The best published upper bound was linear. This changes the exponent to the conjectured one, and the proof gives the exact leading constant, showing the source's balanced assignment is asymptotically extremal.
- The m <= 5 machine checks do not extend by any stated argument, so there was no general-m proof with a missing estimate. That separates it from 350767, where the source proof was complete apart from one estimate.
- The s = 2 mechanism is specific; s = 3 behaves differently.

## Strongest case AGAINST
- Every tool is in the follow-up: Lemma 5, Lemma 6's Bernoulli, Lemma 12's counts, Lemma 13's block AM-GM. The new material is about one page with no new invariant.
- The proof is the Theorem 7 architecture with its finite check made uniform, close to the 350767 and 352895 pattern. 352895 was excluded although its authors also wrote that their methods could not reach the conjecture.
- The authors' pessimistic sentence is weak evidence of difficulty: the work came from an undergraduate research project, and the conjecture seems to have drawn little attention since.
- The lower bound and its extremal assignment are the source's.

## Reasons for the recommendation
No primary theorem plus complete reduction exists: what the printed results leave is the new inequality itself, and the campaign rule says familiar tools and shortness alone do not exclude. The exponent change is the content of the conjecture, not a parameter extension. Confidence is limited because the block method is printed and the residue is a single page.

## Formal (dormant; no dispatch)
Literal endpoint: for the actual SimpleGraph completeBipartiteGraph (Fin 2) (Fin l), `(fun l => (tau (K l) : Real)) =Theta[atTop] (fun l => Real.sqrt l)`, with explicit constants as a corollary. Define P_l as a minimum over m-assignments, and tau as sInf of {k | chi <= k and for all m >= k, P_l = P}, proving the set nonempty (otherwise sInf = 0 makes the bound vacuous). The author plan is sound, with these notes:
- The lower bound must be reproved (its module 8), including general l; a crude constant suffices.
- The literal needs only some constant, so a stronger hypothesis than 2l <= (m-1)^2 can simplify the scalar step. Avoid the log constants in my Case 2; the author's H route is friendlier to formalise.
- My route removes module 2 (Reduce); the author's route keeps it.
- Colour-type bridge: lists in Nat versus arbitrary colours should be stated and paid.
- Theorem 3 is optional and is the same family.

## Inventory
Read in full by contiguous chunks: TASK.txt 0-12892; inherited-denials.json 0-319715 (22 chunks); 2202.03431v2; 2207.04831v2; 2607.16810v1; author candidate and formal plan. Read in part: 2505.05662 (0-11000 plus keyword contexts); 2605.10861 (0-11000 plus contexts); Involve final (opening and keyword contexts).
Rendered: src pp2,3; follow-up pp3,4,8,9,10. Actually viewed: src pp2,3; follow-up pp4,8,9. Rendered but not viewed: follow-up pp3,10.
Network: 3 GET hops of 6, all HTTP 200 PDFs, no redirects, no denials. 2 searches, 2 strings; both responses saved as the next tool call.
Disclosure: search responses are stored with non-ASCII glyphs as backslash-u escapes, stated at the top of each file. Native, transient and writer resource peaks are unknown; no universal cap-compliance claim.
