# H012 PC4 review disposition: retain hypothesis, defer engine

2026-10-08. Native Astra protocol and mathematics reviews completed; independent
Claude Opus5.5 cost/prior-art review completed. Raw Opus report retained in
H012-pc4-opus-raw.md. Root checked the main source and corrects the overstatements
below. No experiment, implementation or Lean theorem added. Improvement NONE.

## Root decision

Do not implement/run H012-pc4-diagnostic-v1.md in this wave. It is preserved as
a concrete protocol, not discarded or silently replaced. Correctness on an
isolated root is insufficient to assess whole-query pruning; the experiment
does not independently decide whether that root is empty. Saturation on a
satisfiable instance is expected and cannot be called a practical refutation
failure. No convincing gain prediction or distribution of early certificates
was supplied. Building two algebra engines (closure and replay) just for this
node would currently prioritize infrastructure over the main objective.

This is a resource-priority decision, NOT a theorem that PC4 cannot improve
ECDLP. A concrete early-node pruning distribution/cost argument, or a cheap
experiment with independently known emptiness and an actual traversal-work
prediction, could reopen it. Existing low-degree slice processing is not such
an improvement. Broader ideation should continue rather than inflate this engine.

## Primary evidence independently checked by root

[Petit--Kosters--Messeng, PKC2016](https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf)
§3.3 already uses smooth multiplicative-subgroup domains represented by low-degree
power chains together with summation polynomials. §4 tests two-point decompositions.
Table4 reports corrected Magma step degrees4 for n1=1..5,5 for6..9,6 for10..11.
The metric omits steps without pair reduction; it is not a minimum PC refutation
degree. §5 leaves asymptotic complexity unresolved and reports limited practical
performance. Root read the PDF text and requested the p12 table screenshot.

These are prior-art findings, not a current impossibility theorem or proof of
degree growth for our m5 unsatisfiable systems. The three distinctions matter:
solving versus refuting, m2 versus m5, and different domain/chart representations.
We make no novelty claim for power chains, polynomial calculus or branching.

## Mathematical review: real degree drops, but no early-node bound

Native Astra /root/h007_additive_relations found no PC4-closed proper subspace
containing all inputs/excluding1 for a substantial class of empty root cosets.
Static original-multiple counting is inadequate: terminal S3(U,u+z,r) has only
U^2*z^2 at total degree4. Multiplying the first-square gate z^2-v by U twice
and subtracting yields degree<=3, which is eligible for further multiplication.

One FREE coordinate in an m2 chart gives a genuine positive control. With other
coordinate fixed to c, F(z)=S3(u+z,c,r) has degree<=2. For quadratic F normalize
z^2=s*z+t. Each quadratic power-chain gate y-v*w, together with already derived
affine remainders for v,w, derives an affine remainder for y via products of
degree<=2. At boundary z^d=eta the remaining affine relation either is a nonzero
constant, or fixes z=z0 with F(z0)!=0, precisely when gcd(F,z^d-eta)=1.
This derives1 at degree<=2, including nonsquarefree F. Linear/nonzero-constant F
are simpler; F identically0 gives no contradiction with a nonempty domain.
This can prune an arbitrarily large last-coordinate coset. It does NOT bound
the frozen FIFO queue work, nor provide earlier pruning across five domains.
Direct degree2 modular powering/gcd already handles this control cheaply.

## Corrections to raw cost review

- For fixed degree4 and n=O(log B), closure has a polynomial-in-log-B upper
  bound per node in field operations. Whole-tree visitation and useful-row yield
  are the missing quantities. All preprocessing, bit costs, memory, rank and
  verification remain paid; favorable O(B^2) linear algebra is not a proved
  complete collector. N~q alone does NOT prove constant useful yield or rank.
- The suggested residual-grid scale B^(7/2) comes from a uniform complete-level
  heuristic N/V, not a necessary theorem that almost all such nodes must refute.
  DFS may find a witness early; variable stopping, uneven grids and failure
  distributions matter. No universal refutation-rate requirement accepted.
- Twist order is 2p+2-q, which is ODD when q is odd, not even as the raw report
  says. Anti-Frobenius plus rational implies2-torsion and henceO in E(Fp).
  Subset extraction does not equate raw full-chart roots to rational full-arity
  decompositions. Irrational cancellation can leave a smaller rational subset;
  the multi-chart/leaf verification policy is essential. No negligible-extra-root
  probability is established, and none is granted for a selected coset.
- Bi~q^(1/5), N=product Bi|p-1 with q~p forces bounded cofactor (p-1)/N under
  constant-factor asymptotics. This is very restrictive; existence of a growing
  admissible prime/full-prime-order curve family and cheap generation remain
  unproved HERE. A bounded cofactor need not itself be11-smooth. No assertion
  about a solved/open global number-theory problem is needed for our limitation.
  One reused smooth subgroup weakens the restriction but changes the challenge
  and still requires reviewed domain/symmetry/yield costs. No secp transfer.
- Raw brute-force10^4--10^5 event estimates and predicted cap exhaustion were
  not measured or derived in the frozen ledger. Matrix capacity/upper bounds
  do not prove the brute-force comparison. They are not accepted runtimes.
- Suggested m2 ladder changes domains/family and degree measure. Failure there
  does not prove m5 failure; success does not show earlier-node pruning. For
  ell3 the gate count is2 per level, not the raw n=k1+k2 expression. Full paid
  setup, emptiness check and multiple targets may exceed the total cap. This
  proposal is retained as a possible diagnostic, not authorized as a replacement.

No broad conclusion is inferred from a finite example, matrix dimension, generic
lower bound or literature regularity statistic. The missing candidate-specific
gain evidence, rather than compilation or proof counts, determines next work.
