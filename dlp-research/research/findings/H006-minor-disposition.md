# H006 minor mechanisms: corrected equivalence; decoding review pending

Factory Opus supplied the retained H006-minor-mechanisms-factory-raw.md. No code,
experiment or Lean proof was supplied. The algebraic equivalence is promising
as an explanation of what the named minor search actually does; it is not a
new algorithmic improvement. Prior art includes Cheng's elliptic-code/subset-sum
connection, https://arxiv.org/html/cs/0507026, and the evaluated-minor procedure
https://arxiv.org/abs/2310.04132. Root opened both primary sources; the raw report
admits that list-decoding and folded-code prior art was recalled, not inspected.

Independent review split:
- Native Astra /root/h002_arithmetic_ideas: exact minor/group-sum equivalence,
  conditioning, fixed/adaptive test probabilities and explicit hashing Mechanism A.
- Factory Fable: interpolation/quotient yield and folded translation Mechanisms B/C,
  primary applicability assumptions and complete repeated-attempt cost.
Native review COMPLETED; Fable decoding review remains live. Both read-only,
no trials/edits/children. No minor diagnostic is authorized.

Root objections supplied BEFORE acceptance:
1. Exactly 1/q probabilities for iid unrestricted scalars need qualification when
   points are required nonzero/distinct and the pivot is conditioned invertible.
   The all-nonzero-path argument covers choices using previous boolean outcomes
   under a frozen distribution, not arbitrary matrix-value-dependent pivoting.
2. Expected collision count does not alone establish constant success or the
   stated complete upper bound. Need dependence/second moment, recovery and setup.
3. Row-equivalent full maximal minors preserve information-set zero patterns.
   A blanket claim that arbitrary UK minors never yield relations is too broad;
   smaller non-systematic minors need their own interpretation.
4. Minor values being computable from points means no additional input
   information; it does not exclude computationally useful algebraic structure.
5. B uses both field-size/group-order notation and two meanings of e. Its
   N=Omega(q) conclusion and charged repeated attempts need derivation. An
   upper-bound decoder cost does not prove a runtime lower bound for all decoders.
6. Translation by a nonzero point in a prime-order group has order q. A partial
   folded block is not a complete orbit; divisor/code-space invariance and the
   assertion that zero sets must be unions of blocks cannot be assumed.
7. Published-table arithmetic, Poisson spread and cofactor assumptions in the
   raw report are unverified hand estimates, not experiment evidence.

Current ranking: check exact algebraic equivalence first; determine whether the
actual interpolation mechanism has a useful regime second. No credible gain
has survived yet. Generic lower bounds, NP-hardness of worst-case code problems,
and failures of these particular procedures are not coordinate-aware impossibility.

## Accepted native Astra corrections and paper result

For N=d+l distinct affine points and D=dO, d=3n', the evaluation code has
dimension d. A dual generator K=[A|I] with identity columns at R_i requires
the complementary S columns to be an information set: sum_j S_j != O.
With this fixed valid pivot, completing a k-minor by complementary identity
columns and dualizing information sets proves exactly

    det A[alpha|beta]=0 iff sum_alpha R_i-sum_beta S_j=-sum_all S_j.

The complementary degree-d divisor is principal precisely when its group sum
vanishes. Schur complements inherit this predicate through their invertible
denominator pivot. Algebra survives value-dependent pivoting; the sampling law
does not automatically survive. This is known in substance from elliptic codes,
not a new attack. For any invertible U, maximal minors instead satisfy
det((UK)_T)=det(U)*det(K_T); their zero sets ARE preserved.

Corrected A model: q is prime subgroup order, Q=mP!=O, iid unrestricted scalar
a_j,b_i, fixed families of k-subsets with 0<k<l=d. Predicates
L_(alpha,beta)=sum_(j notin beta)a_j-m*sum_alpha b_i
have nonproportional coefficient vectors for distinct pairs, hence pairwise
independent zero events, each probability1/q. Let G impose distinct/nonzero
points and a specified valid pivot. Pr(G^c)=O(l²/q), for l=O(log q).
Fixed F-predicate success conditioned on G is <=F/(q Pr(G)), not exactlyF/q.
Boolean-only outcome-adaptive paths admit that fixed all-nonzero branch bound;
coordinate/value-dependent selection and arbitrary batching do not follow.

With M subsets per side, collision count Z has mu=M²/q,
E Z²=mu²+mu(1-1/q), so Pr(Z>0)>=mu/(mu+1-1/q).
Any useless pair has both scalar sums zero, probability1/q²; union bound M²/q².
Conditioning on G loses O(l²/q). Thus M=Theta(sqrt(q)) gives constant useful
success and fresh rounds yield expected O(sqrt(q)) work and memory, not a win.
Recover m=sum_(j notin beta)a_j/sum_alpha b_i and verify.

Paid work per round: O(l log q) point construction, O(l²) replacement differences,
O(l) first subset, about2M incremental additions, expectedO(M) hashing (or
O(M log M) sorting), normalization/encoding, scalar labels and verification.
Memory O(M+l²). No-collision rounds must be repeated. Raw constant2sqrt(2q)
is withdrawn. A matrix is unnecessary; optional construction/elimination adds
polynomial work in l. Suitable l divisible by3 and k near l/2 allow enough subsets.

Also NOT accepted: Poisson spreads from pairwise independence; field-operation
lower bounds from counts of tested minors; automatic rho/mixing interpretation
of an unspecified pivot walk; broad closure from deterministic coordinate features.
No numerical check warranted for this paper equivalence alone. The possible
remaining gain needs an explicit value-dependent or implicit batched algorithm.
Primary review sources: https://arxiv.org/html/2310.04132v1 and Cheng above.
No Lean theorem; best supported ECDLP baseline unchanged.
