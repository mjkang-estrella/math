# MRC: the full one-lattice reduction remains unresolved

Myeongjin Kang; no affiliation. 2026-10-16. Original prose CC BY 4.0; original code MIT.

**UNRESOLVED_FULL_MRC. No acceptance, contribution PASS, or count increment.**
The full target is the byte-frozen `original-scope.md`: one total computable map from arbitrary positive circuit equations to complete finite lattice order tables, preserving solvability exactly as finite-algebra congruence representability. Neither a map nor a proof that none exists was obtained. This note gives the exact available reduction and three barriers to proposed upgrades. These are supporting deductions, not a substitute theorem.

## 1. Source contracts and the missing quantifier

Let R be the set of codes of nonempty finite lattices that occur as the ENTIRE congruence lattice of a nonempty finite algebra of a finite finitary signature. Invalid table codes can be rejected computably. We use the pinned characterization manuscript, family206, at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

Its graph theorem `f:criterion` gives a semidecision procedure for R. For each candidate finite carrier, enumerate all lattice-colored complete graphs and test separation, the join triangle inequality, and connectivity under all label-decreasing selfmaps. The theorem's converse uses the connectivity clause to exclude additional congruences; separation and the triangle inequality alone do not do that.

The source's `n:circuit-template`, `n:template-bound`, and `t:weighted-realization` jointly give the following statements. Fix one sufficiently large absolute cohort stock S. Given a positive circuit C, compute t=t_S(C) and N=Phi(t). Whenever C has a positive solution v, there EXISTS a literal weighted template F, constructed using v, with |F|<=N. F is a subgroup interval and is representable. Every sufficiently small finite-algebra representation of F gives another solution of C with small value variables. Concretely, an algebra of size m gives a solution whose entries are at most 60^m m!.

The logical form is

  for every C, [there exists v satisfying C] implies
  [there exists F of size <= N(C), representable, with the prescribed reading].

It is NOT

  for every C, compute F_C before deciding whether C has a solution.

This difference is explicitly maintained in the source's full `n:undecidable` proof. The companion negative-solution manuscript supplies a nonrepresentable lattice, but does not provide the required circuit-to-lattice construction either. Its global Palfy–Pudlak equivalence is not silently used pointwise.

## 2. The exact bounded-use oracle reduction (technical)

The positive-circuit solvability predicate is weak-truth-table reducible to R. Here this means a Turing computation with an input-computable bound on every oracle query. It is not asserted to be a total truth-table computation on arbitrary false oracle answer strings.

On input C:

1. Compute N(C) as above and enumerate every finite lattice order table with at most N(C) elements.
2. Ask the R oracle about every one of these finitely many tables. The entire list of query codes is computed before the answers.
3. For each YES table, run the source finite graph witness search. All those searches halt for the TRUE oracle. Take m>=1 to be the maximum resulting carrier size.
4. Put Q=60^m m!, and test every assignment in {1,...,Q} to every value variable of C, including auxiliary gate variables.

If a positive solution exists, its literal template F has at most N(C) elements, so its table occurs in step1 and receives YES. The carrier found for F has size at most m. The source simultaneous reading therefore gives a solution of C with values at most Q, which step4 finds. Conversely, any assignment accepted in step4 is an actual solution. This proves correctness and termination with the true oracle.

The maximum code in step1 is computable from C, establishing the use bound. The fact that m is not bounded computably from C is exactly why this proof does not produce a finite truth table whose postprocessing halts for EVERY oracle answer vector: a false YES on a nonrepresentable table makes its witness search run forever. This is not a defect in the valid oracle reduction; it is a scope boundary on its use.

Since positive circuit solvability is c.e.-complete and R is c.e., this establishes the complete c.e. weak-truth-table degree under the stipulated source contracts. It is a direct repackaging of `n:undecidable`, not a substantial nomination.

## 3. Literal finite-group synthesis cannot be the missing map

Suppose a proposed algorithm outputs, on EVERY input circuit C, the full subgroup interval [H_C,G_C] of two actually constructed finite groups H_C<=G_C (and halts). Then every output is finitely representable, independently of C. Thus that algorithm cannot satisfy MRC.

For completeness, let G act by left multiplication on its finite left-coset set G/H, and use each group element as a unary operation. Invariant equivalence relations correspond exactly to subgroups K with H<=K<=G: the class of H is K/H, and all other classes are its left translates. More explicitly, for an invariant equivalence theta, K={g:gH theta H} is a subgroup. Closure follows by applying one left translation to each equivalence; inverses follow similarly. The theta-class of any gH is gK/H. Inclusion, hence the lattice order, is preserved. Consequently Con(G/H) is the full interval [H,G]. There are finitely many unary operations.

Apply this to the unsatisfiable circuit x+1=x. Every genuine finite symmetric-group template still has a finite coset representation. Thus filling its unknown weights with arbitrary convenient positive integers does NOT turn the source's conditional template into a negative instance when the circuit is inconsistent. A successful construction must sometimes output an abstract lattice that has no group realization; it cannot uniformly output actual group intervals and only decorate them with formal arithmetic labels.

This obstruction allows arbitrary group sizes and construction methods. It rejects that route, not MRC.

## 4. Finite local diagrams do not impose fullness

A second route sought to assemble all required comparison gadgets as a finite lattice diagram, then take a finite completion. The essential problem is that an embedding of this diagram into a congruence lattice need not exhaust that congruence lattice.

Precisely, let L be any finite lattice. The classical Pudlak–Tuma finite partition embedding theorem gives an injective lattice map i:L -> Eq(X) for some finite X. Let A be the algebra with carrier X and EMPTY signature. Then Con(A)=Eq(X). Every equation and inequation between terms in the named elements of L is preserved by i: an induction on terms handles equations, and injectivity handles inequations. Every order relation and its negation is preserved as well.

Hence even the complete finite meet/join diagram of a nonrepresentable L has a realization among named congruences of a finite algebra. Requiring finitely many such distinguished local gadgets, even faithfully, cannot by itself distinguish representability from mere embeddability. The pinned family206 supplies the existence of a negative L, so this is an actual separation under the stipulated assumptions, not a hypothetical warning.

The statement here uses the unbounded lattice language with meet and join. It makes no unsupported claim about a particular embedding preserving named ambient 0 or 1. If those constants are desired, a separate endpoint-preserving version must be invoked or proved. The obstruction already applies to the attempted unconstrained named-gadget construction.

What the source graph criterion adds is its global closure condition (iii), over ALL edge sets and admissible maps, which forces every congruence to be one of the named theta_a. The proposed synthesis has not supplied a finite lattice table for which this global condition enforces the arithmetic and is realizable whenever the arithmetic is consistent.

## 5. Even strong oracle completeness plus computable AND/OR is not enough

One possible abstract shortcut was to combine the bounded-use reduction with operations on representable lattices which model conjunction or disjunction. The following elementary computability example shows why completeness under a bounded-use reduction and even BOTH exact Boolean operations do not by themselves force many-one completeness. It is a method comparison, not a claim about which lattice operations exist.

Fix a standard acceptable numbering of partial computable functions and its infinite diagonal halting set K={e:phi_e(e) halts}. Define

  alpha = sum_(e in K) 4^(-(e+1)),
  A = {q in Q : q < alpha},

using any computable bijective coding of rational numbers by natural numbers. The set A is c.e., because partial finite sums increase computably to alpha and q<alpha iff some partial sum exceeds q.

K is truth-table reducible to A. To recover K(0),...,K(e), for each i<=e and every possible binary prefix b_0,...,b_(i-1), query

  q(b,i) = sum_(j<i) b_j 4^(-(j+1)) + 4^(-(i+1)).

This is a finite, input-computable nonadaptive query list. Following the answers along the unique prefix branch yields the correct digits. If i is in K, alpha>q for the correct prefix: K has a member beyond i, so the remaining tail is strictly positive. If i is not in K, the tail is at most (1/3)4^(-(i+1)), hence alpha<q. Every possible answer string defines some branch, so the postprocessing is total. Since A is c.e., it has complete c.e. truth-table degree.

Both Boolean operations are computable on rational codes:

  q and r in A  iff max(q,r) in A;
  q or r in A   iff min(q,r) in A.

Nonetheless K is NOT many-one reducible to A. If f were such a reduction, the computable selector s(x,y) choosing the index with the smaller rational f-value would have the following property: whenever at least one of x,y belongs to K, the selected one belongs to K.

No such selector for K exists. By the standard simultaneous recursion theorem, construct distinct indices x,y for programs which know x,y and compute s(x,y). The x-program halts (on every input) exactly when s(x,y)=y; the y-program halts exactly when s(x,y)=x. Distinctness is obtained using the ordinary padding form of the recursion theorem. If s chooses x, then y is in K and x is not; if it chooses y, then x is in K and y is not. Either case contradicts the selector property. Therefore no f exists.

This argument is self-contained apart from the standard simultaneous recursion/padding theorem. It does not assert priority; lower cuts and semirecursive selectors are classical. Its purpose is to make the failed general inference exact: even c.e. truth-table completeness and computable conjunction/disjunction need not yield the one-output reduction required in MRC. Therefore a genuine lattice-specific synthesis argument remains necessary.

## 6. Remaining mathematical obligation

A sufficient constructive route would compute a complete abstract lattice table L_C directly from the circuit syntax, prove that each integer solution furnishes an actual full-congruence representation of precisely L_C, and recover a positive solution of C from every finite-algebra representation of L_C. Both directions must use the same fixed table, with no solution-dependent table selection.

The source finite size ceiling guarantees only finitely many possible isomorphism types for solution-valued literal templates. It neither gives a uniform algorithm selecting the required type nor shows that a chosen completion of all local constraints has exactly those representations. A finite computable candidate list would already require a separate soundness theorem and would still have to be compressed to ONE output by a suitable operation. None of these unproved bridges is adopted.

No universal counterexample to MRC follows from Sections3–5. They exclude the actual attempted literal-group, local-diagram, and generic reducibility shortcuts. The full frozen target remains unresolved, and the campaign count is unchanged.
