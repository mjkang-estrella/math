# r530 handback: fixed twenty, zero qualified survivors

Lane agent: Claude Opus 5.5, high effort, no children, no Lean, no programs for mathematics. Root alone adjudicates.

BOTTOM LINE. Zero qualified survivors; no FULLCANDIDATE.md and no DORMANT plan, because I do not assert any target survives.
Three complete ordinary arguments exist (PROPOSALS.md), each with a stated zero-credit recommendation that root may overrule:
352895 (Dirichlet, cheap Lean), 372582 (Weil, expensive Lean), 381174 (refutation via KPS, very expensive Lean).
None is independently reviewed. Two conjectures labelled open in MathDB are already proved in their own sources.

Gates: L=literal bound and read; S=source depth; O=ordinary; P=prior; N=novelty; Sig=significance; F=formal (literal Lean);
I=independent review; A=acceptance. I and A are UNPAID for every ID and are not repeated below. No credit is claimed anywhere.
Literal provenance for all twenty: literal-bindings.json (chunk path/hash, 1-based line, raw line/hash, newline, raw token/hash,
decoded statement/hash). L is PAID for all twenty. A recorded park is not an open-status certification.

## Worked targets

352895 Totient congruences. S: 2112.05649v2 Sections 1, 3.2 and Conjecture 2 read as text. O: author-complete proof,
PROPOSALS.md, three cases, two-prime step. P: one search, no hit; surfaced Springer article unreadable (NETWORK-STOP.md), identity
unconfirmed. N: unqualified. Sig: routine adaptation of source Proposition 3.5, zero recommended, dissent recorded. F: cheap
in Nat; needs mathlib Dirichlet, totient multiplicativity.

352894 Merca sigma_0. S: Conjecture 1 and Corollary 1.2 "Conjecture 1 is true" read; text range 14000-25344 containing the
Corollary's proof NOT read. O: my own short Dirichlet/valuation argument agrees (see below), not separately written up. P: source-own public result. N/Sig: zero. F: not pursued.
Argument summary: for p|A, exponent is forced to beta if beta<alpha, otherwise choosable even; a large-prime cofactor gives
k<=1+sum v_2(beta_p+1), and v_2(beta+1)<=min(floor(alpha/2),beta) when beta<alpha pays the required primes.

318354 GJZ gcd. S: 0903.3767v3 Conjecture 1.1 and Theorem 1.1 statement read; proof not audited. O: my p-adic reduction found the
same r=2 mod phi(C)C mechanism before reading it, and on its own pays only the cases v_p(C(2n,n))<=1; v_p>=2 is not independently paid. P: source-own
public result, Cao-Pan confirm it. N/Sig: zero. F: not pursued.

372582 k-PL primes. S: Conjecture 4.1, Definitions 2.6-2.7 and Section 4 read. O: author-complete proof given Weil's bound, PROPOSALS.md.
P: one search, no hit; recurrence character-sum literature unread. N: unqualified. Sig: routine Weil application, zero recommended. F: expensive, Weil absent.

381174 Balan-Wang. S: Section 5 and Conjecture 5.2 read. O: author-complete negation at k=3 given KPS, PROPOSALS.md; KPS body unread,
attributed. P: one search; 2607.06249v1 keyword-checked only, no mention; final journal unread, not requested. N: unqualified. Sig: complete application of KPS, log-only, zero recommended. Source's k=1 n^{-3/2} sentence false by the simplex, correction zero. F: very expensive.

370850 Zeckendorf termination. S: Definitions, Propositions 2.3-2.4, Example 4.5, Conjecture 4.6 read. O: NOT resolved. Literal gap: the algorithm is defined in
the proof only for weakly decreasing c, and Example 4.5 extends it informally (borrow, carry if possible). Literal also admits c1=0
outside the standing c1>0; c=(0,0,1) never terminates under that reading, a domain correction, zero. Hand orbit recorded for
c=(1,0,0,1): (1,1) maps after borrow, borrow, carry-at-zero to the same pattern shifted by 5 positions, so it does not terminate, consistent with clause 3.
Routes tried: (1) periodic-orbit families; (2) G/lex potential for (c1,c1+1,1); (3) zero-padded c. Unpaid: exact algorithm definition; uniform nontermination for
every non-weakly-decreasing c, k>=4; termination for (c1,c1+1,1) and (c1,0,1); nontermination for all c2>=c1+2. F: finite orbit certificates cheap once defined.
Note the arXiv header shows v2 dated 28 Oct 2026; PDF internally compiled 8 Oct 2025.

320444 Bounded-offset digit sums. S: Theorem 2 statement, Section 6, Proposition 1, Conjecture 3 read; Lemmas partially. O: NOT resolved. Literal "C<=b^{r+c} for any integer c" is false as worded:
(b,r,c)=(2,2,-1), k=3 needs n=7=k+4 but C<=2; correction zero. n=0 trivializes c=0 mod r if allowed. Computed exact lower family: k=b^t-1,
n=b^t+e, e>=2 gives s_b(kn)=(b-1)(t+v_b(e-1)), so C>=b^{r-1}+2 is forced for t with t+r-1 matching the target residue, unless the e=1 value 2t(b-1) happens to hit it; at b=r=2 this is exactly the source's k+4.
Routes tried: (1) weight-two multipliers b^a+1 and carry counts; (2) Gelfond exponential-sum error, too weak since lambda>1/2 at b=2; (3) the source's weight-three relation. Unpaid: residue coverage for arbitrary k and (b,r), a generalization of the source's multi-page b=r=2 case analysis.

## Parked after literal review only (original bodies unread; one-line reasons)

360008 weak Weyl-sum: incomplete sums with q>>N, sharp-Weyl-type difficulty, no mechanism. PARK.
354425 Skolem exponential local-global: Bi-Skolem decidability-level. PARK.
349982 finite-support corank: inverse Littlewood-Offord machinery, literal states no resolution; possible later public work unchecked. PARK.
347350 Narayana block repdigits: linear forms bound each fixed m only; uniform all-m has no mechanism. PARK.
342048 covering radius with k interior points: equality characterization, no route. PARK.
344707 Guo-Schlosser: the literal itself reports Jana-Kalita confirmation; not verified, zero by literal report. PARK.
338173 Cluckers quasi-homogeneous Igusa: degenerate case open-type, no route. PARK.
336679 Lang badly approximable: flagship Diophantine. PARK.
381308 roots-of-unity sums (Myerson): flagship-level for n>=4. PARK.
325848 zero digit in products: q=3 already asks 2^k ternary digit behaviour of Erdos type. PARK.
370721 PD-group fibring, 370433 Lie algebra diameter, 358196 verbal width: deep group theory, literal hypotheses only. PARK.

For all parked IDs: F not assessed beyond noting no route; P/N unqualified.

## Process record and disclosures

- Complete TASK.txt (149,320 chars, ten chunks) and complete inherited-denials.json (293,077 chars, twenty contiguous chunks) read before network use.
- History: 927 of 929 allowlisted files checked after protected-name filtering; 2 skipped before open; all hashes matched; one apparent ID hit was a timestamp fragment, so no applicable prior disposition (history-access-inventory.json).
- Search: 3 calls, 3 query strings (tool takes one query per call), each precharged and each full response saved in the next tool call.
- GET: 8 plans; 7 PDF successes; g8 rejected by the guard on a cookie redirect cycle, then network stopped. See NETWORK-STOP.md and guard-ledger.jsonl. No retry.
- Sources read as pdftotext text only; no visual page or figure inspection. No final-version equivalence is claimed for any arXiv text.
- Deviations: (1) one direct `ls -la` of my own plans directory outside the runner after the plan writes; (2) get_g8 wrapper exited 0 despite guard exit 1, so its receipt exit is misleading, disclosed in NETWORK-STOP.md; (3) bootstrap output was persisted by the harness to a tool-results file outside the lane and only its 2 KB preview was shown; I relied on the runner-chunk reads instead. Native tool telemetry, transient and writer peaks are unknown; no universal process-compliance claim.
- Peers transitive-bunkbed-reach-formal-deepseek-r20 and expanded-corpus-r531 not accessed. No writes outside this lane. No credit requested.
