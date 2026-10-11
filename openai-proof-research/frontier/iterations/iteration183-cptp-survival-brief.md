# I183: cross-paired two-path survival

Work in `/home/mj-kang/Documents/Dev/math/openai-proof-research`.
Read AGENTS.md, source contract/catalogue and actual relevant statements.
All OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`
are stipulated true. Eight accepted, two remaining. No truth audit or
lowered contribution gate.

Exclusive writes:

- `frontier/iterations/i183-cptp-survival.md`
- `frontier/experiments/i183_cptp_survival/`
- `frontier/sources/i183_cptp_survival/`

No agents, shared ledgers, staging, commits or publication.

## Original brief, verdicts and parent response

Read the full I182 original assignment, report, analytic attempt and
parent disposition. I182 was assigned E182: the controlled three-edge
alternating-half extension. It proves the reduction lemma to the
derived graph G' = G - V(C), shows the topological half (A-containing
matching with Hamiltonian complement) is always payable under the E182
hypotheses, and leaves the survival half UNRESOLVED. E182, E181, H180
and L179 all remain open.

Authenticate package `frontier/experiments/i182_controlled_extension/`:

- report `6035bffd8b69ba08bf6a148fdd314bd704824e6bdd1942469afb0d343596ebc6`;
- seal `6fcbd83ab618636826cb2c9d7f71d18d22a316fcc12772501dc6fbac7668667c`;
- verify182.py `314696445a3e77ad2a6bde12e0cc4826454b70bc7e0529dfd33d9e00c00f2889`.

25 owned, 1,014 strict external, four contexts = 1,018 external/context.
The original freeze already contains the I181 final integration receipt.
Bind all i182-parent evidence: disposition, brief, validator, replay
stdout/stderr, precheck/verification receipts, certificates and the
dispatch archive; additive frozen supplement before final diagnostics
if the I182 final integration receipt arrives after the first freeze.
Never rewrite a freeze. Ancestor Python is opaque hashed evidence, not
implementation. Parent replay PASS: both payloads replay
byte-identically, eight probes blocked, empty stderr, strict bindings
unchanged. Independent parent certificates PASS: 3 patches, 6
instances, 626 reduction-equivalence checks, 5 controlled matchings per
instance coinciding exactly with the helper products.

Known sealed-verifier limitations to avoid repeating: verify182.py does
not byte-check strict bindings (the parent harness supplies that); its
forged-owned-source probe is vacuous because inventory digests are
nested records; the seal was regenerated twice during development
(recorded, not to be imitated — correct scripts BEFORE the exclusive
seal); seal/inventory embed absolute paths. The I183 verifier must
byte-check all strict bindings and contexts itself, with contexts
drift-exempt and recorded (current bytes), matching the mandated
policy.

Separate scoped audits:

1. I182 reduction lemma: deleting half A bijects A-containing perfect
   matchings of G with perfect matchings of G'; Hamiltonian complement
   iff cross-paired acyclic two-path complement; port data read off
   from G'. Verified independently on all 626 retained matchings.
2. Topological half always payable: q in the complete lost fibre gives
   a Hamiltonian completion whose complement contains A; its local
   restriction is q itself, lost type (01;01).
3. Finite certificate: three patches, six instances, 5 controlled
   matchings each hitting exactly survivor fibres 5/6/9, coinciding
   with the three witness-helper products; 9 equal-pairing products
   correctly excluded.
4. Inherited: twelve indexed controls; C171 F=1/14 vs T=-1/2; I172
   G6/G10 nonbraces; first I175 P8; I176 k6; I177 absorption; I178
   relations/completion; I179 lock; parent helper; I180 helper graph;
   I181 patch/reattachment. All previously parent-verified; sealed
   replay covers them here.

Preserve all historical failed stages/empty captures/traces and the
I175 context limitation. No ancestor edit.

## Single primary target E183

Use the EXACT H180 graph/interface hypotheses (fixed 13-vertex exterior
Y; finite connected simple bipartite locally cubic disk X; five
distinct degree-2 boundary ports in order (0,2,1,4,3), colors
(1,1,1,0,1), other degrees 3; gluing simple planar bipartite BRACE;
eleven complete available survivor local fibres; complete lost
P=(01;01); no isolated cycles), the I181 two-square patch, and the
I182 reduction. E183 asks: decide CPTP-survival. Precisely, for p in
complete P using exactly half A of C with q = p triangle E(C) also in
complete P, and G' = G - V(C) with terminal quadruple (a',b',c',d'):

Prove that the nonempty population of perfect matchings of G' with
acyclic cross-paired two-path complement contains a member whose used
cut labels and port pairing form one of the eleven survivor types
(equivalently avoiding lost P=(01;01) and D=(0134;01,34)); or refute
it by a written actual construction meeting every hypothesis in which
every such complement is lost. The report's preferred proof shape:
re-route the lost (01;01) exterior routing of the q-completion inside
the fixed exterior Y to a surviving pairing while preserving the cross
pairing of the two terminal paths. Equivalent auxiliary form: G'' =
G' + {a'b', c'd'} has a Hamiltonian cycle through both contracted
edges with surviving cut usage. The pinned P4 theorem prescribes one
three-edge path only; brace two-extendability prescribes two matching
edges only; neither pays complement pairing plus survival. D168's
bidirectional shortcut remains false.

No new graph tests, parameter/triple sweep, attachment changes or
population expansion. If neither proof nor refutation is achieved,
mark E183 UNRESOLVED and identify the precise missing condition,
sharper than restating CPTP-survival. Return one bounded next action.

## Controls and reproducibility

Mandatory fresh targeted controls in exact order:
0,520,522,524,527,528,530,533,534,536,539,431; C171 F versus T;
I172 G6/G10; first I175 P8; I176 k6; I177 child/absorption;
I178 relations/completion; I179 lock; parent helper; I180 helper
graph; I181 patch/reattachment; I182 reduction/finite certificate.
Two exact rank methods; actual b/beta/c/residual identities. No full
historical population rescan.

Binding D168 transfer/M168 typed fullness fail; rho L Q squared;
failed V containments; isolated toggles; C171 F=1/14 distinct T=-1/2;
S172 remote only; S174/M175 complete exterior controlled fibres/
restricted H_T and ell_G formula, cut breaking outside; A175 exact
geometry 720 finite; I172 high-loss nonbraces/I173 212 saturated
braces. Universal high-loss brace/lower bound/exchange/(T)/Q164
remain open.

Fresh standard library -I -B; immutable complete input freeze BEFORE
diagnostics, successful prevalidation, ONE exclusive seal (correct all
scripts BEFORE sealing; never reseal), read-only replay 8 blocked
probes with a NON-vacuous forged-source check; strict math/control/
full membership byte-checked by the verifier itself before and after;
only four ledger contexts historical drift exempt with current bytes
recorded, never fatal. Retain failures/empties. No absolute paths
inside hashed seal/inventory content. No OS sandbox/clean clone claim
untested. Primary literature reading honest; snippets not proof reads.
Report source dependencies, exact quantifiers, separate original
verdicts, proved/finite/unpaid steps, hashes, runtime, next action.
