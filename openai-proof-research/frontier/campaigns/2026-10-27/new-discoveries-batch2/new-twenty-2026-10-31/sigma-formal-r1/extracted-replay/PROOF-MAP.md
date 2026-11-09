# Checked partial proof map

This is a parked implementation, not a MathDB solution. All theorem names below
are in namespace Sigma365710. No remaining obligation is introduced as an axiom
or a premise of a purported final theorem.

* Basic: sigmaT is the literal Int-valued unordered all-pair degree sum.
  F casts before subtraction. completeBipartite has exactly cross-part adjacency.
  completeBipartite_connected and completeBipartite_cliqueFree prove membership
  in the target graph class with positive parts. exists_maximizing_part proves
  finite integer maximization exists for every n >= 2. sigmaT_singleton handles n=1.
* Identity: pair_variance proves the unordered-pair variance identity, including
  its factor of two bridge to the ordered sum. sigmaT_degree_identity applies
  the actual mathlib handshake identity. sigmaT_deficit_identity proves
  sigmaT G = m(n^2-4m)-nD, with actual edge count and actual squared degrees.
* Attainment: completeBipartite_degree counts actual neighbors on each side.
  completeBipartite_sigmaT proves the formula F, even for a=0 when a<n.
  attained_family_maximum combines literal attainment and finite maximization
  within the complete bipartite family. It makes no claim about other graphs.
* PathExtension: OneEdgeTriple explicitly requires three distinct vertices and
  exactly one edge. path_extension_witness proves the local witness step for
  every external vertex. Its hypotheses are weaker than induced P4: three
  consecutive edges and the missing endpoint edge suffice for this local step.
  No triples are counted by this theorem.

# Exact unresolved obligations

1. Connect deficit G to the cardinality of the finset of 3-element vertex sets
   inducing exactly one edge, under G.CliqueFree 3. Credit Zhou (2004) for the
   ordinary identity; no novelty claim for this identity.
2. For connected triangle-free G not complete bipartite, construct an induced P4
   (all four vertices distinct, exactly the three consecutive edges).
3. Inject two internal triples and one triple for each outside vertex into the
   finset in step 1, proving (n:Int)-2 <= deficit G. PathExtension supplies only
   the local existence part; it does not prove this counting inequality.
4. Prove unbounded integer bracketing: for every n>=7 there exists 1<=a<n with
   16*F n a >= (n:Int)^4 - 16*((n:Int)-3)^2. This is not present in this packet.
5. Derive strict non-complete-bipartite domination, including small orders,
   then the required universal theorem for every maximizing a. The stronger
   classification of all maximizing graphs remains unproved too.

The authoritative ordinary proof and independent source review remain read-only
inputs. The implementation uses no finite graph enumeration to replace a
universal statement. No conditional theorem is advertised as a solution.
