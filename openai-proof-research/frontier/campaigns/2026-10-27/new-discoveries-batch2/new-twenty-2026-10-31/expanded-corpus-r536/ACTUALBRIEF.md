# ACTUALBRIEF: expanded-corpus-r536

Investigator: Claude Opus 5.5. Fixed twenty, IDs per reservation.json. **Zero qualified survivors. No FULLCANDIDATE, no dispatch, credit 0, 58/80 unchanged.** Root alone adjudicates.

Gates for all twenty are ID-keyed in results.json; inventories are in inventories.json; corpus bindings, including the line hash with its trailing newline, are in literals.json and repeated per ID in results.json.

## Outcomes

| ID | Outcome |
|---|---|
| 323671 | Public: Galvin, Graphs Combin. 32 (2016), Theorem 2 and the printed forest deduction. Zero. |
| 335260 | Public: Dvorak et al. 1907.12091, Theorem 5, printed as proving Conjecture 6.1. Zero. |
| 357028 | Source-own: Melczer-Ruza Theorem 22 proves Conjecture 21. Zero. |
| 335751 | Literal false for odd n by parity; source proves the corrected statements. Zero. |
| 370309 | Author-complete explicit proof, recommend EXCLUDE AS ROUTINE. |
| 338609, 365840, 363002, 335240 | Sustained or source-level attempts, PARK with precise gaps. |
| 370091 | Literal has no precise meaning; PARK. |
| 366314, 351545, 369915, 345692, 347514, 368515, 369373, 358546, 355139, 345691 | PARK after the literal; original bodies unread. These parks are not open-status certifications. |

## Routes taken

**323671.** I found a complete elementary proof before searching: source (10) makes X a mixture of Stirling block counts, so total variance plus Harper gives Var X to infinity uniformly in c, and a second Dobinski-tilting route confirms it. The search then located Galvin 2016, and I read its theorem and bridge. Even without the prior, this is a one-page proof from source (10), (4) and Theorem 4.1, so it would fail the requested test.

**335260.** Bregman summed over vertex subsets with AM-GM gives C(G) <= (1/2)(d/e + 2 + 0.5 ln n)^n. The search located Dvorak et al.; their perm(A+I) proof is shorter.

**370309.** For every odd prime p and n >= p(p+1), K_n is not Legendre cordial mod p, so J(n,m)=0 for n >= m(m+1). Character orthogonality makes Q bounded while the zero-sum edges grow like pq^2/2. Tests: classical theory reduces it fully; the source Theorem 3.3 criterion gives it in one line, since T=pq^2+2qr-q+psi grows and S depends only on r and p; so it is the source argument with no new idea. Recommend exclusion. Strongest dissent: a printed, computation-backed conjecture settled with an explicit threshold.

**338609.** Exact unpaid lemma: a discharging certificate of net charge at most 13 per centre that uses integrality, or an explicit periodic set of density below 1/13. The hand lattice values in results.json are approximate partial sums and certify nothing.

**363002.** The free-diagonal F_2 reformulation shows that a common subtournament does not bound the distance by n-a. An arbitrary-pair relabelling lemma is unpaid.

**365840.** Needs an exact positivity threshold for beta_k^d with O(1) control; the source has only computation.

## Lean feasibility

- 370309: finite statement over Legendre symbols with mathlib character-sum lemmas; cheap, but recommended excluded.
- 323671 and 335260: not routed, public. A literal endpoint would need a triangular-array CLT and Bregman respectively.
- 338609: no statement to formalise until a certificate exists.

## Process

Bootstrap and verify-before ran first as instructed. TASK.txt and inherited-denials.json were read completely in contiguous chunks of at most 15000 characters, with ranges recorded. Three searches, three strings, each precharged with its full response saved in the next tool call. Twelve charged GET hops, eleven payloads, one redirect, no new denials. No failed receipts. No mathematical programs were run; the lattice values were computed by hand. No figures were viewed. Disclosures are in inventories.json.

Sources used: [Galvin 2016](https://www3.nd.edu/~dgalvin1/pdf/journal/asymptotic_nor_J.pdf), [Dvorak et al.](https://arxiv.org/abs/1907.12091), [Melczer-Ruza](https://arxiv.org/abs/2211.15492), [Sedlar](https://arxiv.org/abs/1704.00964), [Andoyo](https://arxiv.org/abs/2509.09528), [Bozeman et al.](https://arxiv.org/abs/1803.01933).
