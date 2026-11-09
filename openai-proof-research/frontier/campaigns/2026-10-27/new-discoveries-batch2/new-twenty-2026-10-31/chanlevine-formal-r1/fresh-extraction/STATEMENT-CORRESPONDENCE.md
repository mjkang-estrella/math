# Statement correspondence — partial round 1

All manuscript line numbers refer to expanded-corpus-r127/sources/txt/1804.03322.txt (arXiv v2), read only. The copied ordinary proof is PROOF.md. There is no unconditional Lean theorem resolving 338887 in this packet.

| Source text | Formal definition or proved statement |
|---|---|
| Example 3.11, lines 1035–1056: advance rotor, move along new edge | Dynamics.target and Dynamics.fire (namespace ChanLevine). true encodes the old right rotor; firing then moves left. false advances to right. Config.fire is the natural-chip version; Config.lift_fire proves its agreement when legal. |
| §3.6 cycle vertices v_k, k in Z_n, n ≥ 3 | ZMod n, with [NeZero n] for finite sums. The eventual unconditional theorem must instantiate this instance from hn. No rotation quotient is taken. |
| Configurations x.q, integer chip ambient | SignedConfig; Config has natural chips and Bool rotors, and Config.lift embeds it in the signed ambient. |
| Definition 4.5 trajectory edges, legal finite executions | Step requires x(v) > 0 and performs fire. Reach is the reflexive transitive closure, so an empty execution is allowed. Existence of a nonempty execution is exactly existence of a first Step. |
| Definition 4.6 common legal descendant | Related is precisely existence of a common Reach descendant. |
| Definition 4.7 components | component c is the set of configurations legally related to c. On recurrent configurations recurrent_related_iff proves equivalence to mutual reachability. General confluence is not silently assumed. component_eq_of_mutual proves equality of these sets from mutual reachability. |
| Definition 5.2(i), (ii), lines 2254–2262 | Recurrent is existence of a legal first step AND return reachability from every legally related SIGNED configuration. The specialised cycle test is a separate predicate; its equivalence is the unproved Prop CycleTestBridge. |
| Definition 4.8, lines 1637 onward | RecurrentComponent requires a legal-relation component and a diverse forward, backward, or two-sided infinite walk. Diversity means each vertex fires infinitely often. The recurrent-configuration to recurrent-component bridge is part of AmbientBridge and remains unproved. |
| Level = total chips (review: cap = 0, s = 1) | level is the signed sum; chipLevel is the natural sum; level_lift proves agreement. level_fire, level_reach, level_related prove preservation. |
| §8.3 weight: left edge 1, right edge 0 | weight = sum k*x(k) plus sum (if q k then 0 else 1) in ZMod n. weight_fire, weight_reach, weight_related are proved. No integer representative is needed for the weight sum. |
| Cycle test (Theorem 7.4), directed cycles on C_n | CycleTest states the facing-pair and the two constant-rotor Hamiltonian conditions. It is NOT the definition of recurrence. CycleTestBridge remains an exact Lean Prop. |
| Explicit representative at level m, weight i | canonical puts m at 0 and left rotors at indices 1 through i.val. canonical_level is proved; CanonicalTest remains unproved. |
| Unique C_{n,m,i}, §8.3 | C is the actual legal-relation component of canonical. It is provisionally named: membership in the required recurrent fibre is proved only under CycleTestBridge, CanonicalTest, ConnectedFibres. existsUnique_component_conditional proves an actual ∃! statement about component sets under those premises. No uniqueness is asserted unconditionally. |
| r(C) counts recurrent configurations in that component | r uses Nat.card of the literal recurrent configurations lying in C. component_finite proves this type finite without a recurrence characterization. Signed nonnegativity, needed to identify this with all source recurrent configurations, remains in AmbientBridge. |
| Conjecture 8.3, lines 4127–4129 | mathdb_338887_conditional_full includes component uniqueness, recurrent-component status and the requested equality, conditional on seven named Props. |
| gcd(n,m,i) for i mod n | Nat.gcd (Nat.gcd n m) i.val. Changing a representative by n leaves this gcd unchanged. Equality of counts for equal gcds is exactly constancy on the gcd fibres, i.e. “depends only on gcd.” |

No source theorem is imported as an added logical assumption. Ordinary source results cited in PROOF.md have not been formalized here. Pending semantic and counting steps are explicit function arguments to conditional theorems. The actual unconditional theorem named mathdb_338887 is not yet supplied.
