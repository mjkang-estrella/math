# Independent computational proof of the four-variable prefix bound

Type: fully explained computational proof, conditional on the documented small Python verifier implementation and runtime. This is not a Lean proof, not a human-only analytic proof, and not an acceptance or priority decision. Independent adversarial review is still required.

## Literal endpoint and source

For every positive integer m, indexed integers 0 <= a_i <= m-1 (i=1,2,3,4), and integer 0 <= K <= m-1, define

S = sum_{j=0}^K sum_{T subset {1,2,3,4}} (-1)^(4-|T|) floor((j+sum_{i in T}a_i)/m).

The endpoint is S >= -3 floor(m/3). Repeated entries are allowed. The empty subset occurs once, with positive sign. No other dimension, extremizer classification, recurrence, or full Conjecture 17 is proved here.

Thanatipanonda–Wong, JIS 21 (2018), Article 18.1.8, Section 4, pp.14–15 independently poses this endpoint, without the divisibility qualification imposed in a later example of Conjecture 17. Its Theorem 15 proves only -2 floor(m/2)-floor(m/3) <= S. The frozen primary text and PDF are `frozen/sources/wong-current.*`. Onphaeng–Pongsriiam, JIS 20 (2017), Article 17.3.6, Definition 1 p.2 expressly permits a multiset; Theorem 9 and its proof pp.14–19 give the weaker general two-sided estimate 2^(ell-2) floor(m/2). Their even-ell sharp statement is the upper endpoint. Reading that proof does not supply the requested lower endpoint. Its actual body is frozen as `frozen/sources/pong11.*`.

## Exact reduction, valid for all parameters

Put H=K+1. Then 1 <= H <= m, and conversely every such H determines an allowed K. For a subset sum s, put F(s)=sum_{j=0}^{H-1} floor((j+s)/m). Since 0 <= s <= 4(m-1), every j+s lies in [0,5m). Thus its floor equals the number of thresholds lm it reaches, for l=1,2,3,4. For an integer threshold lm, the number of j in [0,H-1] with j+s >= lm is precisely

C_H(s+H-lm), where C_H(u)=max(0,min(H,u)).

Indeed, j ranges from max(0,lm-s) to H-1 if that lower endpoint is <= H-1. Counting gives the displayed formula. At u=0 the count is zero; at u=H the count is H. No strict/weak boundary is lost. Therefore F(s)=sum_{l=1}^4 C_H(s+H-lm), and S is its signed sum over all sixteen indexed subsets.

Independently, Euclidean division s=qm+r, 0<=r<m, yields F(s)=Hq+max(0,r+H-m): there are exactly max(0,r+H-m) indices crossing the next multiple. This agrees at r+H=m and at r=0. In particular F(0)=0 because H<=m; the empty-subset term has not been dropped from the encoding. When H=m, F(s)=mq+r=s, and alternating this linear subset sum gives S=0 (each indexed a_i has coefficient (1-1)^3). When m=1 all entries and K are zero and S=0. These endpoints require no exception in the query.

Permuting the four labels bijects subsets and preserves signs and sums, including repeated entries. We may therefore impose a<=b<=c<=d. No rotation, complement, generic-position, or strict-chamber reduction is used. Introduce integer t>=0 and 3t<=m<=3t+2. These conditions are equivalent to t=floor(m/3), by integer division with remainder. The negation of the endpoint is exactly S < -3t, equivalently S<=-3t-1 since S is integer.

`mapping.py` parses the frozen SMT-LIB file without an SMT library, expands simultaneous lexical lets, and compares its eighteen assertions to an independently constructed list: six m,H,t conditions; four nonnegativity conditions; four upper bounds; three sorting conditions; and the negated endpoint with all 16*4 signed clips. It normalizes integer sums and constant products, retaining ite expressions and normalized comparison conditions. It also checks all seven declarations are nullary Int symbols and disallows extra command kinds. Each of the seventeen assertions actually used by the proof is matched to this list. A proof may omit an assumption; it may not invent one. `query-map.json` records this correspondence. This is a symbolic identity check, not a finite-m experiment.

## Certificate and lexical scope

The certificate is the frozen 6,626,456-byte `z3-proof.sexpr`. Its origin in Z3 is not trusted. No Z3 executable, library, SMT solver, or second solver is invoked by the checker. `inspect.py` parses parentheses and simultaneous SMT-LIB lets into a hash-consed DAG. Each binding right-hand side is evaluated in the outer lexical environment; only the body sees all the new bindings. Bindings shadow correctly and IDs are shared rather than textually substituted with accidental capture. The final verifier independently reparses and reconstructs the exact entire DAG, comparing every node and edge with `dag.jsonl`.

There are 22,672 total shared nodes and 12,459 reachable proof-rule nodes. Only reachable dependencies matter. `check.py` first verifies expression types, operator vocabulary, rule arities, and that EVERY non-conclusion argument of every proof rule is itself a recognized proof node. Unknown or ill-typed rules fail; none are skipped. Nodes are checked in topological ID order. Every rule has a validity flag and a set of undischarged hypotheses. An unsupported local rule or invalid dependency propagates failure to the root.

## Independent rules and their soundness

Asserted formulas must match the independently mapped input query. A hypothesis introduces its exact formula as a tracked assumption. Modus ponens checks P and P=Q conclude Q; transitivity checks the entire equality chain. Congruence checks identical function heads and equality of every argument, either syntactically or by a supplied equality premise. Z3's definitional `~` is accepted only as equality in these checked chains and definition applications; it is not a blanket trusted rewrite.

Rewrites use exact affine normalization or Boolean normalization. Integer ite subterms may be treated as independent integer indeterminates keyed by their identical DAG ID. This abstraction proves identities for arbitrary values of those subterms and therefore for their actual values. It never assumes that different ite terms are equal. Products must be constant times affine expressions; unsupported nonlinear operations fail.

Comparisons are converted to integer linear inequalities. Strict integral A>0 becomes A>=1. For integer variables, g*B+c>=0 with positive integral g is equivalent to B+floor(c/g)>=0. Clearing positive denominators, dividing by the positive gcd of variable coefficients, and orienting a relation against its exact integral complement yield canonical atoms. Affine equality is the conjunction of both weak inequalities. Boolean connectives are checked by a reduced ordered Boolean decision diagram. Unrelated arithmetic atoms are treated independently: this weakens proving power and cannot manufacture an arithmetic implication. Non-affine integer equality may remain an opaque atom. Each Boolean rule has its own 100,000-node bound; hitting it is failure, not success.

All 5,540 unit-resolution applications and 145 not-or-elimination applications are checked as exact propositional entailments of their supplied premises. All 243 definition-axiom clauses are checked as tautologies. For a lemma whose supplied premise proves false under hypotheses H, the checker discharges exactly those h for which not C propositionally implies h, where C is the lemma conclusion. If R is the remaining set, then R and not C imply every original hypothesis and hence false, so R implies C. This validates all 644 hypothesis-discharge steps without assuming a discharged hypothesis globally. Hypothesis validity is distinguished from being closed; closed means valid with an empty residual set.

The 128 fresh definitions are checked globally. Each must have exactly the two clauses (not P or z=u) and (P or z=v), with a unique fresh `z3name!` symbol absent from the query. Their dependence graph is acyclic, and every extension symbol appearing in the reachable proof is accounted for. Hence every assignment to the original integers extends uniquely by z=ite(P,u,v) in dependency order. These clauses are true in that extension. An apply-definition rule must name exactly the corresponding ite and z. This is a conservative definitional extension, not a new mathematical assumption about the original parameters.

For EVERY one of the 1,329 arithmetic lemma applications, the checker conjoins the supplied premise conclusions with the negation of its conclusion and derives an exact contradiction. A true conjunction and a false disjunction split into their component constraints; equalities split into opposite weak inequalities. No opaque arithmetic lemma is whitelisted.

The arithmetic algorithm uses integer rows A*x+c>=0. Positive denominator clearing and the gcd/floor rule above preserve their integer validity. To eliminate a variable with positive coefficient p in one row and negative coefficient n in another, it adds (-n) times the first row to p times the second. Both multipliers are positive; the variable cancels. It retains unaffected rows. Dropping rows cannot invalidate a subsequently derived contradiction. A row with no variables and a negative constant is impossible. Thus every returned contradiction is sound over the original integer assignments. Different bounded elimination orders may find different consequences; twelve deterministic tie orders are tried when needed. Each attempt is limited to 4,000 prospective rows and 150 eliminations. Failure to find a contradiction is failure to validate that rule, never an UNSAT inference.

For example, one arithmetic step combines c+d-m>=0, m-a-b-c-d-1>=0, a>=0 and b>=0 to give -1>=0. The actual checker performs this reasoning for all emitted arithmetic premises in exact Python integers/Fractions, not by floating-point linear programming or a call back into Z3.

The complete local rule counts are: 1,466 rewrites; 17 assertions; 134 modus-ponens steps; 227 hypotheses; 1,503 congruence steps; 128 introductions of definitions; 955 transitivity steps; 243 tautological definition axioms; 5,540 propositional resolution steps; 1,329 arithmetic lemmas; 644 hypothesis discharges; 128 definition applications; 145 not-or eliminations. Every local check passes. The root is node 22671, its conclusion is false, it is valid, and its residual hypothesis set is empty.

## Conclusion and trust boundary

If the literal endpoint had a counterexample, symmetry and the exact floor-to-clip reduction would produce an integer assignment satisfying the mapped query. Extend this assignment by the checked acyclic definitions. Induction through all checked proof rules makes the root false true, a contradiction. Therefore there is no counterexample, for any positive integer m, and the literal endpoint follows.

The finite coverage is of the entire proof DAG, not of a bounded range of m or a sample of chambers. Trusted components are the stated mathematical reduction and rule-soundness argument, the shipped parser/mapping/checker/verifier code, Python's ordinary exact integer/Fraction/container semantics, and the local execution environment. Hashes bind bytes; they do not establish mathematics by themselves. No proof assistant kernel has checked this argument, and the checker requires independent adversarial review. The source PDFs/text extractions and source interpretation are separately auditable trusted inputs. Prior art, novelty and campaign eligibility remain HOLD.

`final_verify.py` checks all frozen originals and copies, the manifest, independent exact DAG reconstruction, query correspondence and a fresh full rule replay in a separate guarded execution. It writes only the excluded verification receipt and rechecks all other hashes after replay. See that receipt for actual exit statuses, command lines, resource limits and outputs.
