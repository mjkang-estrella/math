# Independent scoped formal review — T088P133, round 1

**Verdict: PASS_SCOPED_SUPPORT. REQUIRED repairs: none.** The immutable implementation faithfully proves the requested deterministic real-algebra portion of original Proposition B. Its universal statements, proof terms, positive denominators, strictness mechanism, nonvacuity controls and disclosed coverage pass this review. This is the first independent formal-support review, not a repeat mathematical correctness or contribution review. No full formalization, mathematical correctness, contribution, acceptance, count or release verdict is awarded.

Runner: Codex / GPT-6.1-Sol / high / default service tier. The original mathematical statements and operative proof operations at upstream fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated true; they were not audited. This verdict follows the present source/type/axiom/use-site audit and fresh copied build, not the parent's intake or the previous full correctness verdict.

## Object and exact statement

The unchanged geometric target remains: every convex 4-polytope with nonempty interior and at most six **actual** facets satisfies V4(ΠK) ≤ (160/3)V4(K)^3, equality iff simplex; every exactly-six-facet case is strict, including nonsimple, repeated-Gale, zero and boundary cases. No geometric assertion is a Lean declaration in this package.

The reviewed implementation is `t088p133-formal-v1`, with independently supplied anchors recorded in `anchors.json`. Both original Lean file hashes, the source archive, FINAL, manifest and outside report matched before code parsing/execution. The frozen scope/proof hashes also matched before reading them. All original author/reviewer manifest file hashes matched; those inventories include private bodies that were hashed but not semantically read in this review. The original formal packet has exactly 24 entries excluding its manifest (21 files), and its read-only verifier checks 940 recorded original entries.

For **all** real α, β, p, q, d, P, N, `rational_mixture_lt_one` has exactly the premises

    α>0, β>0, α+β=2, 0<p, p<1, q=1-p, d≥0, P>0, N>0,
    2*d*p^2<P, 2*d*q^2≤N,

and conclusion

    (1+d)*(p*α/(α+P/p)+q*β/(β+N/q))<1.

The products, square exponents and parentheses in the elaborated type match this expression. There is no implicit distribution, dimension, box constraint, bracket-sign premise, desired-slack premise or upstream theorem axiom. The non-strict wrapper changes the first moment and conclusion to ≤; all other hypotheses are the same. The A,B wrappers are slightly more general in allowing p,q≥0 with q=1−p, provided A,B>0 are separately supplied. This does not extend the mixed-case rational wrapper to zero denominators.

## Audit of every support declaration

All 21 declarations were checked against both source and fresh elaborated output. The three definitions were additionally printed with bodies in `evidence/review-types-axioms.log` and locked by a definitional-equality contract. They bind seven explicit real arguments in the order α,β,p,q,d,A,B.

1. `firstBracket`: F=pAβ+qBα−dαβ. It is an actual expression, not a nonnegative quantity by definition.
2. `secondBracket`: G=AB−d(pαB+qβA), again with no built-in sign.
3. `mixture`: M=(1+d)[pα/(α+A)+qβ/(β+B)]. Lean's total division is present, but every inequality using it here derives positive denominators.
4. `firstBracket_decomposition`: for arbitrary seven reals, α+β=2 and q=1−p alone give F=pβ(A−2dp)+qα(B−2dq)+d(2p−α)^2. It needs no sign hypotheses as an identity. Substitution β=2−α,q=1−p gives the same polynomial on both sides.
5. `secondBracket_decomposition`: α+β=2 alone gives G=[αB(A−2dp)+βA(B−2dq)]/2. Neither q=1−p nor d≥0 is needed for this identity.
6. `cleared_slack`: q=1−p alone gives (α+A)(β+B)−(1+d)[pα(β+B)+qβ(α+A)]=F+G. No denominator or sign premise is concealed.
7. `slack_identity`: the preceding rational slack identity assumes q=1−p and explicitly α+A≠0,β+B≠0. It does not assume either bracket's sign.
8. `firstBracket_nonneg`: α,β,p,q,d≥0, both normalizations and 2dp≤A,2dq≤B make each residual product and square term nonnegative. This is a valid polynomial replacement for the original square-root/Cauchy–Schwarz argument; it proves the same sign at the use site.
9. `secondBracket_nonneg`: α,β,A,B≥0, sum2 and both residual bounds suffice. Its absence of hypotheses on d,p,q is legitimate: the explicitly assumed residual bounds contain the needed information.
10. `secondBracket_pos`: α,B>0, β,A≥0, sum2, 2dp<A and 2dq≤B give G>0. The first summand is strictly positive because αB(A−2dp)>0; the other is nonnegative. Strictness is derived, never assumed as G>0.
11. `mixture_le_one`: α,β,A,B>0 imply α+A>0,β+B>0; F,G≥0 and their positive product denominator give M≤1. The exact assumptions match the elaborated type.
12. `mixture_lt_one`: the first residual bound is strict. F≥0 and G>0 give M<1 by the same positive denominator. This pays strictness by a moment inequality, not by continuity.
13. `moment_lt_iff`: for arbitrary d,p,P with p>0, 2dp²<P iff 2dp<P/p. Multiplication by positive p preserves direction; there is no division by d.
14. `moment_le_iff`: the same equivalence for ≤; the theorem is also applied at (q,N) after proving q>0.
15. `conditional_means`: from 0<p<1,q=1−p,P,N>0 it proves q>0, P/p>0,N/q>0,p(P/p)=P,q(N/q)=N. The conjunction's grouping is correct. Its name is shorthand for algebra: it does **not** prove any conditional expectation formula or identify any law.
16. `rational_mixture_lt_one`: exactly the requested universal P,N interface, deriving A=P/p,B=N/q positivity and the strict/weak residual bounds through declarations 13–15 before applying declaration 12.
17. `rational_mixture_le_one`: exactly the non-strict interface, applying declaration 11. It cannot imply strictness in general, as its equality control demonstrates.
18. `positive_sum_two_bounds`: positive α,β with sum2 give α<2 and β<2, without an additional normalization premise.
19. `one_sided_lt_one`: all real a,d,M with 0<a<2,M>0,2d≤M give (1+d)/(1+M/a)<1. Omitting d≥0 is correct and stronger. Indeed d≤M/2<M/a, since M>0 and a<2; the denominator is >1. This reasoning remains valid for arbitrarily negative d. The implementation's polynomial argument proves da<M without dividing by d. The independent control uses d=−2 and obtains −1/2.
20. `p_one_bound`: positive α,β,sum2,P>0,2d≤P imply the p=1 reduced expression (1+d)/(1+P/α)<1; α<2 is derived by declaration 18. It asserts no probability equals one.
21. `p_zero_bound`: the symmetric reduced expression (1+d)/(1+N/β)<1 under N>0,2d≤N. It asserts no probability equals zero.

At d=0 the strict mixed theorem still has P,N>0 and thus A,B>0; A−2dp=A>0 and G=AB>0. No step divides by d, requires d>0, or infers strictness from a merely nonnegative coefficient. Some assumptions are redundant or weakenable (for example P>0 follows from the strict moment and d≥0); no claim that every hypothesis is individually necessary is made.

## Faithful mapping to original Section 5

The entire frozen proof was read, including the preceding normal form and subsequent certificate/final assembly. In original Proposition B, d=D(b)/(2(n+1)), p=Pr(Wb>0), q=1−p, P=E Wb⁺,N=E Wb⁻. The preceding unformalized probability argument supplies q=Pr(Wb<0), A=P/p,B=N/q and the conditional Laplace majorization. The auxiliary inequalities are exactly 2dp²≤P and 2dq²≤N; the first is strict in the mixed case. Lean assumes those derived real inequalities and does not prove their origin.

With A=P/p,B=N/q, the implemented F/(αβ) equals P/α+N/β−d. The implemented G/(αβ) equals

    (AB/(αβ))*[1-d*(p^2*α/P+q^2*β/N)].

Thus the implementation's cleared slack is exactly the original normalized two-bracket display multiplied by αβ>0. There is no swapped α/β, omitted p or q, reversed moment conversion, or extra strict probabilistic assumption. `SemanticAudit.lean` independently proves both normalized identities and their combination with `slack_identity`, including all nonzero divisors. It also proves a scalar composition: **if** an arbitrary real L is at most the unscaled rational bracket, the strict wrapper yields (1+d)L<1 using 1+d≥0. L is not defined as an expectation; this control leaves the probability interface exposed.

For p=1 and p=0 the original proof first reduces to a one-sided Laplace bound. The endpoint theorems match those reduced expressions directly. They do not plug P/p or N/q into the mixed theorem when a weight is zero. The independent endpoint identity also checks (1+d)a/(a+M)=(1+d)/(1+M/a) under a,M>0. These statements are useful deterministic support for precisely the unchanged use site.

Eight explicit Lean type contracts fix the exact strict/non-strict wrappers, both moment conversions, conditional-mean algebra and all three endpoint interfaces. The definition contract fixes the bodies of all three definitions. Two copy-only semantic mutations compile the support successfully after adding (i) an extra d>0 premise to the strict wrapper, or (ii) the desired mixture conclusion as an extra premise to the non-strict wrapper. Both are rejected by the independently fixed contract with a type mismatch. This demonstrates detection beyond prose mapping or merely accepting a successful module build. These controls are bounded regression evidence, not an exhaustive semantic mutation suite.

## All 20 original controls and independent arithmetic check

Every control's elaborated type and axiom list was read; all compile. The concrete conjunctions are statements in ℝ. Where α=β or p=q, a single numeric proposition supplies duplicate identical hypotheses.

- `rational_example_hypotheses`, `rational_example_bound`, `rational_example_value`: (α,β,p,q,d,P,N)=(2/3,4/3,1/3,2/3,3/2,1/2,4/3); exact value 12/13. The first moment is strict and the second equals 4/3. The bound actually invokes the universal strict theorem.
- `zero_d_bound`, `zero_d_value`: α=β=1,p=q=1/2,d=0,P=N=1, A=B=2; exact value 1/3, through the same universal theorem.
- `nonstrict_equality_hypotheses`, `nonstrict_example_bound`, `nonstrict_cannot_imply_strict`: α=β=d=1,p=q=P=N=1/2 yields value 1 with both moments equal; the non-strict wrapper is applied and a strict conclusion is refuted.
- `missing_first_moment`: α=β=d=1,p=q=1/2,P=1/8,N=1/2 gives 13/10; even the weak first moment is false, all other strict-wrapper hypotheses hold.
- `missing_second_moment`: same α,β,p,q,d with P=1,N=1/8 gives 17/15; the first moment remains strict and only the second bound is removed.
- `missing_sum_normalization`: α=β=2,d=1,p=q=1/2,P=1,N=1/2 gives 7/6; only sum2 fails.
- `missing_alpha_positivity`: α=−2,β=4,d=1,p=q=1/2,P=3/4,N=1/2 gives 24/5.
- `missing_beta_positivity`: α=4,β=−2,d=1,p=q=1/2,P=1,N=3/4 gives 14/3. In both positivity failures the final rational denominators are explicitly nonzero, so the failure does not exploit totalized division.
- `missing_weight_normalization`: α=β=1,p=1/2,q=1,d=0,P=1/8,N=1/4 gives 6/5; p still lies in (0,1), and the moments hold.
- `missing_probability_range`: α=β=1,p=2,q=−1,d=0,P=1,N=2 gives 7/3; only p<1 is removed among the requested hypotheses, and the denominators remain nonzero. This is an algebraic countermodel with a negative q, not a purported probability law.
- `endpoint_examples`: both endpoint wrappers are actually used at α=β=d=1 and positive moment 2.
- `endpoint_zero_d`: one-sided theorem applied at a=M=1,d=0.
- `endpoint_upper_boundary`: a=M=2,d=1 gives equality 1, exhibiting the strict a<2 boundary.
- `endpoint_zero_moment`: a=1,d=M=0 gives equality 1, exhibiting the M>0 boundary.
- `endpoint_missing_moment`: a=M=1,d=2 gives 3/2 while 2d≤M fails.

Independent Python `Fraction` checks reproduce all ten mixed numerical configurations, every retained hypothesis, the omitted hypothesis's failure, and **all** nonzero p,q and final denominators, including cases whose Lean statements do not explicitly list every divisor. These examples neither construct probability/polytope realizations nor establish necessity of every assumption.

## Fresh compilation, proof trust and source restrictions

A newly extracted copy of the independently anchored source archive was used under this review's work/. The reviewed implementation rebuild script received explicit `--cache` and `--lean`; it compiled support, controls and all 41 type/axiom checks into new outputs. All three commands exited zero without warnings, and the fresh source hashes, dependency pins, compiler hash, axiom reports and complete type-log bytes match the sealed successful implementation evidence. This is our fresh build, not reliance on the parent's earlier build.

The compiler is Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52, executable SHA256 e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550. Mathlib is d13f23b723b8a846827a245b89c10fc7d3f11612; all eight auxiliary revisions and mathlib's transitive lock match the receipt. Only this package's support/control/audit files and independent review controls were compiled. The existing precompiled Lean/mathlib/dependency cache is trusted and read-only. HEAD pin checking is not full binary authentication or a clean-source mathlib rebuild; neither was requested or claimed.

All 41 original declarations, **including definitions and controls**, and all 15 independently named review declarations report only propext, Classical.choice and Quot.sound. Sources/imports were inspected: no sorry, admit, custom axiom, unsafe declaration, native_decide, imported new-conclusion axiom or hidden geometric premise occurs. Axiom-output inspection complements source inspection; compilation alone is not the semantic verdict. The independent audit compiles without warnings after correcting its own tactic development attempt; the failed attempt remains in excluded work/ and does not alter the implementation. All 11 original copy-only artifact controls were freshly reproduced with their expected reasons. This review also supplies its own externally anchored read-only verifier and copy-only controls.

## REQUIRED versus OPTIONAL observations

**REQUIRED: none for this scoped algebra submission.** No author revision or new review round is requested. All excluded obligations below must continue to be disclosed when this support is integrated; this is a coverage limit, not a newly required theorem.

**OPTIONAL:** carry the independent normalized-bracket/type contracts into later regression checks, and keep the endpoint's valid negative-d generality explicit. The current prose already discloses those identities as mappings rather than existing implementation declarations. Their absence as original named declarations is not a gap because the exact rational wrapper already provides the requested interface; this review independently checks the mapping in Lean. No manuscript edits are performed or assessed here.

## Coverage and unchanged outstanding mathematical interfaces

Entirely unformalized remain: actual-facet geometry and nonzero middle coefficients; mixed volumes, variational attainment, coarea and Gamma–Dirichlet; distributions, log-concavity, HNBUE and expectation-to-mixture majorization; the ten-pattern coefficient certificate and its probabilistic interpretation; continuity, zero/repeated-knot assembly and the derivation of a strict moment; simplex equality; every-six-facet geometric strictness and the final projection-body theorem. Even the review's scalar composition does not prove an expectation inequality. No best auxiliary constant, all-n threshold, broader-dimensional result or new contribution inference is made.

The implementation's README/COVERAGE/PROVENANCE/NOTICE retain this boundary. The earlier full correctness verdict and bounded contribution decision are external process history, not Lean axioms or this package's formal verdict. Parent owns integration and later gates.

-- copied alteration with reseal
