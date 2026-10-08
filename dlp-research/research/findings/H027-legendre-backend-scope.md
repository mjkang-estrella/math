# H027 hypothetical character oracle: exact reduction, charged upper bounds

2026-10-08. NEW native Sol reviewed Opus CardB against full primary texts; root
checked the reduction and balancing calculations and read BBUV Table1 and cost
discussion. The claimed failure even with a free oracle is withdrawn. No actual
ECDLP oracle extraction or improved solver is supplied. The separate proposed
unmarked-surface extraction fails H027-polarized-character-falsifier.md.

## Exact conditional scalar-field reduction

Let Q=kG and suppose a supplied oracle returns F(tG)=chi_q(1+t²), with chi(0)=0.
Assume q=1 mod4 and choose iota²=−1 in the SCALAR field Fq. For c≠0,

`F(cQ+aG)=chi(k+(a−iota)/c)*chi(k+(a+iota)/c)`.

The chi(c²) factor is1. Any distinct x,y can be realized by
c=2iota/(y−x), a=cx+iota. All scalar arithmetic, sqrt(−1), point generation and
oracle calls are paid; Fp remains the separate coordinate field.

Choose anchor x0 with nonzero chi(k+x0). An initial query for distinct x0,x1
either returns zero, giving k in {−x0,−x1} for exact scalar verification, or
certifies such an anchor. Then R(x)=sigma*chi(k+x), sigma=chi(k+x0), is obtained
for x≠x0; define R(x0)=1 without a diagonal query. Any later zero identifies
k=−x directly. The two possible signs give two backend inputs, one correct.

The extractor must accept generated points or have explicit exceptional dispatch.
If its only excluded scalar parameters are the known0,±iota, precompute those
public points and answer their values1,0,0 before extraction. This does not repair
arbitrary restricted domains or a binary convention hiding unknown zeros.

Complemented sequences are not automatically covered by the source's uniqueness
assumption. An explicit safe cost policy runs both sign branches round-robin at
charged elementary word-operation granularity, including filtering and verifying
any candidate via kG=Q. If the genuine branch completes in T steps, total steps
are at most2T plus proportional scheduling overhead, with at most twice its
space envelope when each branch is capped to that envelope. A runaway wrong
branch must not block a complete search/lookup as one uncharged atomic step.
This is a specified reduction policy, not a claim about complement statistics.

## Source-supported schedules (heuristic upper bounds)

Write the source prime as q and L=Theta(logq). BBUV Table1 and §§3.1–3.4 charge
optimized word-machine time

`T(M)=O(M²+q*log²q/M²)`, `S(M)=O(M²/logq)`.

There are M consecutive oracle answers; logq≪M<sqrt(q) includes the minimizer
M≈(q*log²q)^(1/4), giving O(sqrt(q)*logq) word work. M² is paid table preparation.
The sequence-uniqueness assumption and clustering caveat remain; this is not
a proven unconditional all-input decoder bound. Primary full PDF read by Sol;
root checked Table1 and its explicit upper-bound/word-model convention:
https://cosicdatabase.esat.kuleuven.be/backend/publications/files/journal/3130

The published Kaluđerović–Kleinjung–Kostić paper, §5A3/Table2, charges

`T(M)=O(M²/logq+q*logq*loglogq/M²)`, `S(M)=O(M²/logq)`.

Its arithmetic-subsequence extraction uses the same M answers. Balancing gives
M≈(q*log²q*loglogq)^(1/4) and O(sqrt(q*loglogq)) word work. Sequence distribution
and uniqueness heuristics remain. Sol read §2A and §5, including the paid packed
extraction and amortized search, from the published primary paper:
https://msp.org/obs/2020/4-1/obs-v4-n1-p17-s.pdf

These balances are achieved upper envelopes of particular schedules, not lower
bounds against unlimited/adaptive oracle algorithms. Increasing M above their
balance increases these literal preparation costs, not necessarily every method.

## Complete ECDLP conversion cost and decision

Add M*C_F, query-point generation, scalar-field operations, failed searches and
final verification to the backend ledger. Straightforward generation costs
O(M*logq) group operations. Polylog-cost extraction would leave these query costs
asymptotically below the displayed backend envelopes at their balanced M, but
such extraction has not been supplied. Word work is not an EC-operation count
and supplies no material constant-factor comparison with accepted EC kernels.

Do not downgrade H003/H018 or claim free-oracle impossibility from a restricted
upper-bound algorithm. Retain both the extraction problem and a better charged
recovery schedule as open premises. No numerical test or full-work gain follows.

Access: official ePrint2019/1357 and2020/098 fetches failed; BBUV's full COSIC PDF
and KKK's published ANTS paper were read instead. The detailed2020/098 preprint
remains unread; indexed abstracts were not promoted to full-source evidence.
No experiments, probe imports, source edits by reviewer or new Lean claim.
Verified ECDLP improvement NONE; ordinary square-root reference unchanged.
