# Complete ordinary bridges that earn zero discovery credit

## 358093 — rational integer-point transform

Definition (1), published Robins article pp.157–158, is a sum over precisely P intersect Z^d; Theorem 1.1(1) says evaluation distinguishes the finite lattice-point sets. Theorem 1.1(2) recovers an INTEGER polytope from the convex hull of those points; (3) explicitly dilates rational polytopes until they are integer. Published p.171 Conjecture 1 asks for rational polytopes without that dilation. These actual definitions and statements were read, not inferred from the abstract.

Take d=1, P=[0,1/3], Q=[0,1/2]. They are nonempty bounded full-dimensional convex hulls of rational vertices. For an integer z in either interval, 0<=z<1, hence z=0. Conversely 0 belongs to both. Therefore P intersect Z=Q intersect Z={0}. For EVERY real xi (in particular the prescribed xi*=sqrt(2)/pi), both sums equal exp(2 pi i 0 xi)=1. P differs from Q because 1/2 belongs only to Q. This is an exact refutation in the literal rational-polytope scope with no analytic or transcendence theorem needed.

For any prescribed d>=1 one can also take [0,1/3] times [0,1]^(d-1) and [0,1/2] times [0,1]^(d-1). Both have lattice points {0} times {0,1}^(d-1), so the same argument applies without relying on lower-dimensional polytopes or empty lattice sets.

Why excluded: the transform factors through the finite lattice-point set by its definition; equality of those finite sets is already the source's complete invariant theorem. Distinct rational convex bodies with identical lattice samples refute injectivity immediately. This is a complete routine source-definition bridge, not a newly established invariant theorem. No novelty/significance credit, no Pi plan. The malformed corpus notation is preserved verbatim in provenance; the source supplies the intended P,Q,xi*. The refutation does not depend on changing that intended scope.

## 358013 — the source already refutes the universal NMDS assertion

Lu–Wu define the identical c(b,c), D and trace code in (1.1); their actual Theorem 5 states q=3,5 give [q+1,3,q-1] MDS codes and all other q>2 give [q+1,3,q-2] NMDS. Theorem 4, Table 2, and the weight-to-zero-count proof were read. Thus the universal q>2 statement is false in a publicly printed 2023 source. No new discovery can come from reusing its q=3 exception.

An independent handwritten verification of that exception removes any inference from a title. Work over F_9=F_3[i] with i^2=-1, irreducible because the squares of F_3 are 0 and 1. The roots of x^4=1 are exactly {1,-1,i,-i}: these four distinct roots exhaust degree 4. Thus D={1,i,-i}. For b=u+vi, i^3=-i, so trace(b)=2u=-u. In coordinate order 1,i,-i followed by the extension coordinate, c(b,c) equals

    (u+c, v-u+c, -u-v+c, u).

This is a linear injective map from F_3^3: the last coordinate recovers u, then the first recovers c, then the second recovers v. Hence length 4, dimension 3. If u=0, the first three coordinates sum to zero, so a nonzero word cannot have weight one. If u!=0, a weight-one word would require all first three coordinates zero. The first gives c=-u; the second gives v=-u; the third gives v=u, a contradiction. The choice u=c=0,v=1 gives (0,1,-1,0), of weight two. Therefore d=2, whereas q-2=1. The requested [4,3,1]_3 parameter claim fails. This reproduces the printed exception exactly, so is excluded as an already public result.

## 358052 — exact known theorem, not the neighboring open extension

The source's Corollary 2.13 is precisely conciseness of gamma_r(u_1,...,u_r) for pairwise disjoint non-commutator words, even bounded conciseness. Its proof and Theorem 2.11's proof were read. Let S_i be the set of u_i-values in an arbitrary group G and N_i=<S_i>. Every S_i is conjugation invariant. A non-commutator word has a variable with nonzero total exponent n_i; set its other variables to 1 to see that every n_i-th power of G (and hence of N_i) belongs to S_i. Disjointness of variables gives exact equality between the substituted-word value set and gamma_r evaluated on the tuple S. The source's Corollary 2.3 identifies the generated verbal subgroup with gamma_r(N_1,...,N_r). If the value set is finite, Theorem 2.11, with these N_i,S_i,n_i, makes that subgroup finite. This is the literal definition of concise. No extra hypotheses, endpoint strengthening, or unproved arbitrary commutator-tree step is needed. It is already the source's exact Corollary 2.13, zero credit. The separate outer-commutator extension 358053 was held in completed r310 and remains separate.

## 358269 — public related resolution, with quantifier caution

The original source's Conjecture 5.1 was read. Galvin's 2502.10654, submitted 15 February 2025 and revised 23 January 2026, explicitly identifies the Kadrawi–Levit question and proves arbitrarily large distance of failure from the last coefficient (Theorems 1.3/2.1). The relevant construction and proof coefficient estimates were read: T_(m,t,1) has root, m children, t grandchildren per child, one leaf per grandchild; its independence number is (t+1)m, and its failure occurs at mt+2 for t sufficiently large and t<=m<=2^(t/16). Thus the failure depth m-2 tends to infinity. This is already public and is no new result here.

Caution: the introduction also phrases a stronger exact-each-ell question. The displayed theorem with sufficiently large t and m>=t directly proves unbounded depths, not by itself each prescribed small depth. I do NOT substitute an unbounded subsequence for an exact-all-k quantifier. The corpus's 'arbitrarily chosen k' is ambiguous between these readings. Consequently the entry is a HOLD for precise quantifier reconciliation if exact every k is required; it is a public exclusion for the arbitrarily deep/unbounded reading. No unsupported full-quantifier clearance, and no Pi plan.
