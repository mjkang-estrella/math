# Endpoint-sign lift: exact surviving terms

Myeongjin Kang, no affiliation. Original prose CC BY 4.0. Parent author assistance for structural r53; no independent review, nominee or count change.

The unchanged BUC target is the existence of a finite connected simple bipartite graph F and symmetric W in [0,1] with t(F,W)+t(F,1-W)<2^(1-|E(F)|). The original freeze is `fresh-structural-discovery-r17/excluded-buc-scope.md`. Its early assignment withdrawal did not refute this target. The present calculation resolves one previously tentative lift only.

Let U be any symmetric bounded real kernel on a probability space. Adjoin an independent uniform sign s in {-1,1} to each point and define V((x,s),(y,t))=(s+t)U(x,y)/2. For a finite simple graph J, let v_+(J) count its nonisolated vertices and c_+(J) its nontrivial connected components. Then

    t(J,V) = q(J) t(J,U),
    q(J) = 2^(c_+(J)-v_+(J))

if every nontrivial component of J has an even number of edges, and q(J)=0 otherwise. The empty graph has q=1.

Proof. In the product over edges, the factor (s_u+s_v)/2 is zero unless each edge joins equal signs. Hence a contributing sign assignment is constant on each nontrivial component C. Its edge product is s_C^|E(C)|. Summing the two possible signs on C gives zero for odd |E(C)| and two for even |E(C)|. Divide by 2^|V(C)| and multiply across components. Isolated vertices contribute one. The x-integral separates from these sign averages and supplies t(J,U).

Equivalently, expanding each endpoint sum chooses one endpoint of every edge. Surviving monomials have even choice count at every vertex. Relative to any fixed choice, changing an edge toggles its two endpoints, giving the incidence map over F2. On a connected component its image is precisely the vectors of even coordinate sum, so the required parity is achievable exactly when its edge count is even. Its fiber then has size 2^(|E(C)|-|V(C)|+1). This provides the same coefficient after division by 2^|E(C)|.

For |U|<=1, W=(1+V)/2 is a valid complementary pair. Its normalized two-color density is exactly

    2^(|E(F)|-1) [t(F,W)+t(F,1-W)]
      = sum_{A subset E(F): every component of F[A] has even edge count}
          2^(c_+(F[A])-v_+(F[A])) t(F[A],U).

The empty term is one. This identity includes every homomorphism; no injectivity or type restriction was introduced. Sign reversal on the added coordinate swaps W and 1-W, so their individual densities are equal.

For the stipulated connected 35-vertex, 66-edge source pattern H, the full term survives with coefficient 2^-34. A two-edge path also survives, with coefficient 1/4, and its kernel density is integral (integral U(x,y)dy)^2 dx >=0. Thus the lift does not isolate the source's negative global correlation. Applying k independent endpoint-sign layers gives q(J)^k: the full H term receives 2^(-34k), whereas a two-edge path receives 2^(-2k). This coefficient comparison alone is not an impossibility theorem; individual kernel densities, including vanishing row means, still matter. In particular the source's one-sided density deficit for a nonnegative kernel does not by itself provide the signed proper-subgraph bounds required here.

The finite diagnostic checks this sign coefficient for all 1,099 labeled simple graphs on one through five vertices. It supports arithmetic implementation only. The displayed universal proof is the argument above; neither proves BUC or its negation. Parent read the original BUC freeze and excluded screen in full for this calculation; no new literature search, source-kernel proof audit or global novelty claim was made.
