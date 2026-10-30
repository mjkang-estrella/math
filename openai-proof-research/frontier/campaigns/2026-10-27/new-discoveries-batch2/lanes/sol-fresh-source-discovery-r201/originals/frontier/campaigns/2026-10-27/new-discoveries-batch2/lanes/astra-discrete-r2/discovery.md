# Candidate handoff: the q-Hoggatt Sturm conjecture

**Status: complete written candidate proof; not accepted, not counted.**
No child agents, public writes, git operations, shared edits, or ledger changes.

## Exact source and result

Fang–Zhang–Zhao, *Analytic properties arising from the Baxter numbers*,
[arXiv:2505.05873](https://arxiv.org/abs/2505.05873), Conjecture 4.1, asks whether
`{H_n^[m](q,t)}_{n>=1}` is a Sturm sequence for every positive integer q and
m=2,3. Its definition is the boxed-plane-partition weighted sum in PROOF.md.
The source's Theorem 1.2 proves q=1 for all m>=2. The live arXiv submission
history displayed only v1; the [published JMAA article](https://doi.org/10.1016/j.jmaa.2026.130615)
also presents the q-extension as a conjecture in its accessible conclusion.

The proposed proof establishes, for **every real q>1 and every integer m>=2**,
simple negative zeros, strict interlacing of consecutive H_n, and strict
multiplicative q-separation of the zeros. This implies the full conjecture
when combined with the known q=1 theorem. This is one candidate family,
not separate credits for q, m, strictness, or separation.

## Proof mechanism

Normalize to

    F[N,m](t)=sum_k q^(m*k*(k+1)/2) prod_{j=0}^{m-1}[N choose k+j]_q t^k.

MacMahon's product gives `H_n=F[n+m-2,m]/prod_{j=1}^{m-1}[n+m-2 choose j]_q`.
All normalization factors are positive. Define
`G[N,m]=F[N,1] star F[N-1,m-1]`, with ordinary coefficientwise multiplication.
The exact relation is

    Dq G[N,m](t)=[N]_q q^m F[N-1,m](q^m t).

Garloff–Wagner Theorem 4 supplies both strict interlacing of consecutive G's
and strict q-separation. A residue proof shows Dq preserves strict
interlacing when the larger polynomial has q-separated negative roots.
This closes induction in m. **PROOF.md contains all details**, including
constant/linear boundary cases and every strictness exception in the
classical theorem.

## Strongest objection and bounded novelty investigation

The strongest objection is **routine adaptation or subsumption**: FZZ already
uses this Hadamard induction at q=1. The new argument uses established
q-separation concepts. No novelty is claimed for its general analytic lemmas.
A naive derivative replacement is insufficient: for
`f=(t+9)(t+10)(t+11)`, the q=2 derivative is
`7t^2+90t+299`, with discriminant `-272`. Thus even simple negative roots do
not suffice; the separation invariant must actually be established.
Nevertheless, root should independently judge whether the complete
conjecture resolution meets the campaign's nonroutine threshold.

The following primary theorem bodies were inspected, not merely titles:

- Garloff–Wagner, JMAA202 (1996), Theorem4: the indexed original p800 and
  FZZ Theorem2.1's full restatement match. The original PDF download timed
  out; its full proof was not downloaded. Exact conditions are in PROOF.md.
- FZZ Theorems1.2/2.1/2.2 and full q=1 induction; Conjecture4.1 and definition.
- [Dilks thesis](https://www-users.cse.umn.edu/~reiner/DilksThesis.pdf),
  Theorem3.8 and proof: real-rootedness of H_n^[m](1,t), not the q>1 Sturm claim.
- [Lamprecht](https://arxiv.org/abs/1210.1102), Theorems25/29/30:
  q-Rolle and weighted convolution interspersion; classical ingredients,
  not a statement of the Hoggatt family endpoint. The q conventions differ.
- [Leake–Ryder](https://arxiv.org/abs/1712.02499), Theorem1.7 and Proposition3.6;
  [2026 q-convolution paper](https://arxiv.org/abs/2606.15003), Section2.4 and
  Propositions3.4/3.5: related preservation theory. No Hoggatt endpoint found
  in these inspected sources; this is not a proof of absolute novelty.
- [Mao–Shi](https://arxiv.org/abs/2607.01582), Definition1.1 and Theorem2.4;
  [Liu–Mao](https://arxiv.org/abs/2608.22258), Theorems6.6/6.7;
  [Chern–Shi](https://arxiv.org/abs/2609.33732), Theorems1.1–1.4: log-behavior
  results. Chern–Shi's polynomial variable q in Theorem1.2 is the row
  generating variable; it must not be confused with the two-variable
  Hoggatt specialization here. Their q-refined coefficients in Theorems1.3/1.4
  are related, but coefficient log-concavity does not prove the Sturm claim.
- [Chern–Shi 2606.26950](https://arxiv.org/abs/2606.26950), Theorem1.1:
  a different Cigler polynomiality/positivity problem, not this Sturm claim.

The live [MathDB record368343](https://mathdb.com/p/368343) returned an open
label and empty solutions/comments. Those counts are NOT evidence of novelty.
Its additional references2403.19692 and2212.10586 are false matches: generic
split-polynomial criteria and a distinct Narayana refinement, respectively.
The latter's Conjectures5.4/5.5 are explicitly already resolved in its v2.

Public GitHub issue searches for Hoggatt in PerAlexandersson/RealRooted and
google-deepmind/formal-conjectures returned one q=1-related issue1332 and
zero issues, respectively. These are issue searches, not exhaustive code
searches. Public web searches for Hoggatt/Sturm, q-interlacing, the source
identifier, and Ideosphere did not locate a proof of the exact endpoint.
No authenticated or private registry search was attempted. Exact queries,
URLs, saved-byte hashes, and access limits are in provenance.json.

## Verification and exact remaining gap

- `python checks/hoggatt_exact.py`: PASS, 288 exact rational coefficient
  identities and1,296 normalization instances. Finite corroboration only.
- `python formal/replay.py`: PASS under pinned Lean4.34.1/mathlib commit.
  Three small algebra/order lemmas only; standard3 axioms reported.
- `BRIDGES.md`: precise remaining formal obligations. The full source
  theorem has **not** been formalized, independently reviewed, written as
  a final paper, or subjected to a fresh extracted strict endpoint replay.

There is no identified mathematical gap in the written proof. The outstanding
risks are independent proof validation and novelty/subsumption, plus the
substantial formalization work just listed. Root should review before investing
in the full Garloff–Wagner formal dependency.

## Earlier BBK attack: no result

BBK372432 Conjecture5.1 remains open in this lane. The old simple-pole/eventual
periodicity reduction was read; no all-coefficient positivity proof was found.
A weighted-complete-intersection route fails already at n4,k6. Exact finite
monotonicity checks are retained in `checks/monotonic_scan.*` but earn no credit.
Chern–Wang2601.19845 proves the motivating m1 positivity, not the full
refinement. No excluded target, gcd-normalization defect, finite instance,
or helper is proposed as an outcome.
