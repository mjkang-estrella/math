# I175 parent disposition: five-port decomposition and type boundaries

**Technical only; no ninth nomination. Eight accepted, two remaining.**
The [I175 report](i175-affected-prism-exterior.md) verifies two low-loss
braces and proves conditional structural lemmas. It neither finds a
high-loss octagonal brace nor proves an infinite prism-family rank formula.
Pinned OpenAI premises remain stipulated true.

## Authentication and independent checks

| Object | SHA-256 |
|---|---|
| Report | `7df9e04e808e5f537eef1291b9f323ffd27dfb25c6edd4b76b34d8f23e198ff9` |
| Seal | `42636ad1d8a669c8bee23332d7059e0ba957c3467a343ea2b563fdf346905c31` |
| Verifier | `e09a4daaa655b9482cb3ac5686fce7e0555eb7d857b8d0ce77b063d184be101a` |

Detached anchors, the complete 94-owned inventory, successful-prevalidation
control chain and all 399 non-context external bindings match. Four
separate contexts give **403 external/context entries**.

Parent sealed replay **PASS in 16.19692463602405 seconds**: five
byte-identical payloads, eight blocked probes, empty stderr, unchanged
owned/external/control bytes, complete owned membership and current contexts.

Parent-only DFS and Fraction ranks separately reproduce the three new
complete seven-family records, all 2,460 matching witnesses, the initial
graph's three tight-cut failures, six exhaustive local/exterior packing
products and their actual-anchor rank decompositions. The small examples
have losses 4/6 and full/restricted dimensions 8/5 as claimed.
The parent checks reuse only previously committed parent helpers,
not child implementations. The 720-record boundary scan is covered by
sealed replay, not an independent parent rescan.

Receipts and scripts in `frontier/experiments/` have prefix
`i175-parent-`: `validate.py`, `precheck.json`, `replay-stdout.json`,
`replay-stderr.txt`, `verification.json`, `certificates.py`,
`certificates.json`, and the integration validator/receipt.
Python audit guards are not OS sandboxing. Clean-clone reconstruction
was not tested.

**Replay-context limitation:** unlike the preceding context-tolerant
verifier, I175 requires exact inventory-current hashes of its four
context-only ledgers at startup. The accepted replay was therefore run
before integration ledger edits. A later direct replay in the updated
checkout fails that preparation check despite unchanged mathematical
bytes. All four historical contexts have been verified recoverable
from parent baseline commit
`0cb1adce63798d0cc88db2a33bb3e4e91bb9228f`.
Use a separate historical reconstruction, not a live-checkout rollback
or a changed seal, to reproduce those inputs. That reconstruction remains
untested. I176 is instructed to record inherited context drift and require
current context-byte stability during replay instead of fixed historical
context hashes. This limitation does not invalidate the completed replay.

## Mathematical verdicts

**I174 audit: PASS in the assigned scope.** All 236 Q173 survivor/matching
certificates and 15 I174 complete family records were independently checked.
The entire old search, absorption audit and three-cut census were not
rerun. S174 retains its complete-fibre/exterior-control/type hypotheses.

**P8 experiment: verified in its finite scope.** The order-26 initial
exterior has loss 3. The first two of 14 valid triples produce order-30
graphs with survivor rank 16 and loss zero. Each is a brace certified by
900 perfect matchings, but retains a (3,1) hexagon. Twelve valid triples
remain untested; zero second attachments or surgeries were eligible.
These are not the requested high-loss (3,3) braces.

**Five-port decomposition and sufficient criterion: accepted as proved.**
Cutting a Hamiltonian cycle across the five distinct port endpoints gives
two spanning path packings, with two or four used cut edges and no isolated
cycle. Conversely, compatible endpoint pairings give exactly one cycle.
The survival predicate is determined by the cut set and exterior packing,
so each retained state is the full product of its actual local/exterior
families. It follows that
$$
L=W_X+W_Y+\operatorname{span}\{c_s-c_{s_0}\}.
$$
Disjoint supports give $W_X\cap W_Y=0$; actual anchor relations are still
needed. The connected local bipartite subgraph has zero-projection
degree-kernel dimension $k-1$; the global projected image has dimension 9.
Reaching both with realized survivor differences therefore proves saturation.
Those rank hypotheses have **not** been established uniformly in $k$.

The six finite decompositions have image rank 9. The extra kernel
contribution from anchor relations is respectively 2,2,0,2,0,0 for
P4 first/second, P6 first/second, P8 first/second. Omitting those actual
relations would lose two dimensions in three cases. The parent independently
exhausted the state packings and reconstructed the complete survivor sets.

**M175: accepted with the restricted full exterior family retained.**
For available full types $T$ and survivor types $I$, projection kernels are
the actual sums $K_T$ and $K_I$ of within-type attachment spaces. The
cut equations kill all type totals in a zero projection; complete fibres
realize the reverse inclusion. Thus
$$
\ell_G=\dim\operatorname{diff}(\mathcal H_T)
       -\dim\operatorname{diff}(\mathcal S_H)+\dim K_T-\dim K_I.
$$
Only when every full exterior type is available is the first difference
the ordinary full exterior loss. Proper active subsets can create a
defect, but all-three activation is not logically necessary if $K_I=K_T$.
The K4 example illustrating this last point is nonbipartite, not an
admissible high-loss target. Restricted fibres invalidate the formula.

**A175: accepted using the stipulated prescribed-path theorem.**
For protected deletions $ab,cz$, neighbors $N(z)=\{b,c,d\}$ and distinct
$a,b,z,d$, the path $a-b-z-d$ forces the survivor type omitting $cz$.
The two types using $cz$ come from the corresponding two-edge paths
through $z$, extended to simple three-edge paths. Simplicity and cubic
bipartiteness pay that extension. Every resulting Hamiltonian cycle uses
a protected deletion. This blocks missing types under that local geometry,
not for arbitrary remote interfaces.

## Failures, contribution gate and continuation

The field-convention failure (`rankUV` is an absolute rank) and mixed
coordinate-space failure remain with exact source stages, empty payloads
and stderr. They are implementation failures, not false mathematical
theorems. The rejected genus-one rotation and inherited I174 pre-seal
document transition also remain intact.

The conditional rank criterion and affine-splice correction do not clear
the substantiality/novelty gate; limited literature selections establish
no priority. High-loss braces, universal lower bound/exchange,
prescribed-square exclusion, (T), and Q164 remain open.

[I176's brief](iteration176-uniform-five-port-rank-brief.md) targets an
analytic uniform construction of $k-1$ local directions and nine projected
directions for the first canonical surgery, with explicit packings,
anchors and any strip-extension recurrence. New finite checks are bounded
at $k=10,12$; they cannot substitute for the proof.
