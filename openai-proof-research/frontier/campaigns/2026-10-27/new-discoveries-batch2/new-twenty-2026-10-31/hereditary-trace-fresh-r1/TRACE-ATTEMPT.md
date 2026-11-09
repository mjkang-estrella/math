# 321413: exact source and sustained deformation attempt

Status: promising algebraic counterexample route, **zero credit**. No Lean endpoint, no independent fidelity review, no published-body clearance. The computations below are rational, not numerical matrix sampling. They are not a substitute for the interpretation bridges.

## Restored object

Hoge, arXiv:1104.0904v1, Sections 1–2: over C, C_nd is the simultaneous-conjugation invariant algebra of d generic n by n matrices. C_infty,d is the polynomial algebra on nonempty words modulo cyclic rotation, with symbol Tr(w) of word multidegree. The specialization pi replaces formal traces by actual matrix traces. E is the fixed minimal homogeneous generating system of Lemma 3.2; CE is the polynomial algebra on its 48 symbols (Ta,Tb,Tc,T1,...,T45), embedded by the corresponding formal trace combinations. Lower-case x,y,z are traceless parts of X,Y,Z.

R:C_infty,d -> CE is a multigraded algebra homomorphism, identity on CE, satisfying (pi restricted to CE) composed with R = pi. It is not pi, and the relevant defining ideal is ker(pi restricted to CE), not ker(R).

Definition 2.5 supplies a multilinear identity Tr(X1...X7)=P(X1,...,X7), for n=3 and N(3)=6, with P a sum of products of traces of shorter words. The reduction fixes cyclic representatives to lexicographically least rotations, substitutes the first six letters separately and the remaining suffix into X7, recurses, and finally expresses traces of degree at most six in E. The freedom is any such trace identity, not arbitrary independently chosen changes to high trace generators. The linear system Ax=e1 in Section 2 constructs the allowable affine space.

The fixed S is the four-word tuples of Theorem 4.1, together with the letter permutations prescribed by Remark 4.2. A tuple M represents R(F(M)), where F is the signed fundamental trace identity on four arguments. Minimality means minimal homogeneous **ideal** generation of ker(pi restricted to CE). It does not mean linear independence of words or algebra generation by the tuples. Conjecture 2.10 asks whether these fixed tuples work for **every** reduction of Definition 2.5. This is stronger than Lemma 2.8's genericity statement. The existential assertion in Lemma 2.4 is already proved and is not the target.

## Later sections do not establish the universal quantifier

Theorem 4.1 and Section 5 compute relations for the chosen reduction (the paper points to thesis pages 95–103 for that reduction) and compare Hilbert series after a homogeneous system of parameters. This proves the chosen presentation. It is not an argument that the determinant of every parameterized relation matrix is a nonzero constant. Genericity alone also cannot establish that. Conversely, a generic nonzero polynomial need not have a root unless nonconstancy is shown; that shortcut is insufficient to refute the conjecture.

The paper's warning after Lemma 2.4 allows arbitrary evaluation maps to eliminate a relation. That warning alone is also insufficient: the altered map must come from one admissible multilinear reduction with the prescribed cyclic algorithm.

## Exact calculation at the first relation

The first tuple is M=(111,22,3,3), of multidegree (3,2,2). Its single-trace part is

    -2 Tr(1112233) -2 Tr(1113223) -2 Tr(1113322).

The script trace_degree7.py enumerates every four-tuple of nonempty words of this multidegree, up to argument permutation (234 columns). The 30 distinct cyclic single-trace rows have rational rank 30. Kernel combinations give identities q containing only products of traces, each factor of length at most six.

It then constructs **all** products of fundamental identities of total degree four, five or six with complementary trace monomials to multidegree (3,2,2). There are 243 such columns, of rank 104 in 260 formal trace monomial coordinates. A saved q is outside their span: adjoining it gives rank 105. The space of new decomposable classes obtained from the degree-seven kernel has rank one.

Polarize this q by replacing its three 1's by labels 1,2,3, its two 2's by labels 4,5, and its two 3's by labels 6,7, summing all 3!2!2! assignments. Call the resulting decomposable multilinear identity Q. There are 1374 nonzero terms before specialization. Set

    Delta = -2 Q(1,1,1,2,2,3,3)
            -2 Q(1,1,1,3,2,2,3)
            -2 Q(1,1,1,3,3,2,2).

The exact quotient calculation is

    Delta = -72 q  modulo products of degree<=6 fundamental identities.

verify_exact.py independently reads the saved polynomials and uses SymPy DomainMatrix over QQ: rank(L)=104, rank(L,q)=105, rank(L,Delta+72q)=104. The saved polynomial q has a 16-term rational certificate as a combination of fundamental identities; the generation script re-expands the certificate exactly. There are no floating point rank tolerances.

## Proposed full-scope mechanism and remaining bridges

Start with a good reduction P0. Since Q is a multilinear trace identity consisting of shorter trace products, P_t=P0+tQ is again a trace reduction in the literal sense of Definition 2.5. For the degree-seven tuple M, all shorter traces are reduced identically, so

    R_t(F(M)) = R_0(F(M)) + t R_0(Delta).

If p=R_0(q) is nonzero, the quotient calculation gives R_0(Delta)=-72p. Theorem 4.1 has exactly one generator in multidegree (3,2,2), with no relations below total degree seven. Thus the degree-(3,2,2) part of the actual defining ideal is one-dimensional. Consequently R_0(F(M))=c p, with c nonzero, and t=c/72 makes this chosen relation zero. Other degree-seven tuples have distinct permuted multidegrees, and higher-degree relations cannot generate a missing degree-seven component. The fixed list would then fail even generation at that parameter.

A route to proving p != 0 is available, but is **not yet a formal bridge**: let B be the polynomial algebra on all cyclic trace words of length at most six. Since actual CE has no relations below degree seven, each shorter trace has a unique expression in E. The kernel of B -> CE should be generated by these shorter-trace elimination equations, each itself a trace identity of degree at most six. By the second fundamental theorem these generate precisely the ideal represented by the 243 lower columns in this multidegree. Hence q outside that span gives p != 0. This requires carefully proving the polynomial CE embedding, the restriction/retraction statements, the homogeneous truncation of the second fundamental theorem, completeness of the enumeration, and the multidegree count from Theorem 4.1. No theorem assuming this central identification has been inserted into Lean.

This is a concrete route beyond the genericity and arbitrary-retraction shortcuts: it supplies an exact nonconstant direction with a nonzero coefficient (-72), rather than presuming an exceptional point exists. It has not yet become a source-faithful kernel-checked counterexample. In particular, the ranks and the source presentation theorem are not Lean-proved here. The algebraic argument should receive independent adversarial review before any resolution claim.

## Formalization and prior-art limits

A full endpoint must define words, cyclic trace symbols, the invariant specialization, E including traceless substitutions, admissible reductions and their recursion, the prescribed list, and ideal minimal generation. It must prove the fundamental identities and all finite quotient certificates in Lean, with only propext/Classical.choice/Quot.sound transitively. A lemma parameterized by the unproved quotient bridge would not qualify. No Lean theorem or clean Lean replay is claimed.

The publisher metadata identifies Journal of Algebra 358 (2012), 257–268, DOI 10.1016/j.jalgebra.2012.02.025. The public publisher PDF request returned 403; it was not retried or bypassed. The arXiv paper's later Sections 4–5 were inspected, but published-body comparison remains a mandatory gap. Text searches and Palomar's empty Hoge query do not clear stronger same-object results or unpublished followups.
