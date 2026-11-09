# Second-pass primary depth: no completed endpoint

These are investigations, not accepted discoveries. No Lean theorem, independent acceptance, or novelty clearance is asserted. The ranking concerns the next mathematical work, not significance inferred from runtime. Existing objections remain in inherited-selected.json and results.json.

## Rank 1: 347689, Gao–Li Conjecture 5.3

Read Definition 2.3 and its K3 example, Definition 4.1 and Lemma 4.1 with proof, and Definition 5.1, Proposition 5.1 with its complete five-case proof, and the concluding paragraph and Conjecture 5.3. The primary requires a common recurrent identity at every sink, separately for each possible attachment vertex. Neither a common zero-equivalence class alone nor one attachment suffices. The tree has one added vertex and one edge. Theorem 5.2's last proof paragraph was inspected; its full case analysis was not audited.

**Route A: force the common configuration from the leaf sink.** Let H be G with leaf a attached to v, with G connected and at least two vertices. Suppose H has complete identity c. Stability at any sink other than a gives c(a)=0. With sink a, recurrence forces c(v)=deg_G(v): indeed if c(v)<deg_G(v), every vertex of the nonsink subset V(G) has fewer chips than its degree within that subset (all other vertices are stable with c(u)<deg_G(u)). This is a forbidden subconfiguration, contradicting the burning criterion. Stability gives the reverse inequality. The burning criterion is a standard external bridge here, not proved in Lean or independently audited in a primary reference in this pass.

With sink v, attaching the zero-chip nonsink leaf has no effect on the original recurrent identity at other vertices. Thus if e_v is G's recurrent identity with sink v, the only possible common vector on G is

    b^v(v)=deg_G(v),     b^v(u)=e_v(u) for u != v.

This reduces a putative search for c to one candidate per v. The assertion about leaf attachment follows by the reduced-Laplacian block equations and recurrence of the zero leaf; a full formal proof of the recurrent-configuration bijection is still required.

**Route B: use divisors rather than recompute every sink.** Write S_v=sum_u b^v(u). Since e_v is zero-equivalent with sink v, b^v-S_v*delta_v is in the image of G's full Laplacian. Zero-equivalence of b^v at any other sink s is equivalent to b^v-S_v*delta_s being in that image. Subtracting shows the necessary condition

    S_v*(delta_v-delta_s) is principal for every s.

The classes delta_v-delta_s generate the critical group, so its exponent must divide S_v. This is the same compatibility mechanism as the primary Lemma 4.1, specialized to the forced vector. Conversely this exponent condition and the already known sink-v zero-equivalence give zero-equivalence at all original sinks. For H with an original sink, the leaf row forces its firing potential to equal the potential at v, reducing precisely to G. For H with sink a, solve L_G f=b^v-S_v*delta_v and add a constant so that f(v)=S_v; this gives the required integer solution for H. Thus the lattice part can be isolated from recurrence. No claim that compatibility implies recurrence is made.

For K_m with m>=3, the original identity is m-2 on each nonsink, so S_v=(m-1)^2, congruent to 1 modulo the critical-group exponent m. For an odd cycle C_m, the original identity is all ones on nonsinks, so S_v=m+1, again failing divisibility by exponent m. For an even cycle C_m, the source identity has one zero opposite v and ones elsewhere among nonsinks; S_v=m passes this filter, and the primary's separate firing proof establishes recurrence. These restricted comparisons do not classify arbitrary graphs. In particular, the source already observes that some bipartite graphs fail the property.

**Precise remaining lemmas:** prove the forced-vector/leaf-recurrence bridge from the actual sandpile definitions; then show that any connected nonbipartite G has some v for which b^v either fails the exponent condition or fails recurrence at some sink of H. No general obstruction of this form was proved. There is no justified reduction to an odd induced cycle: recurrence and critical groups need not survive deletion in the necessary direction. Enumerating graphs through ten vertices would repeat the primary's scope, so no graph sweep was run.

Lean burden would include stabilization, uniqueness of the recurrent representative, the burning criterion or its replacement, integer Laplacian/divisor bridges, graph bipartiteness and all attachment/sink quantifiers. A checker for compatibility alone would be a surrogate endpoint. Park, zero credit.

## Rank 2: 341567, infinite strict adjacent sign changes

Read primary Definition 2, Proposition 1 and its proof (equations 2.1–2.4), the final nonvanishing argument, Section 5's Definition 3 and Conjectures 1–2, and Theorem 2 and Proposition 3 with their proofs. The exact recurrence is c_0=1 and

    sum_{k=0}^n c_k/(n+k+1)=0, n>=1.

The primary also proves a nonzero 2-adic norm, hence c_n never vanishes. Its full earlier permutation decomposition was not independently audited. The strict adjacent-sign definition is retained, including N>0. An exact diagnostic through c_32 reports changes at N=1,26, whereas the source's numerical list prints 1,27. This indexing discrepancy is recorded only as a diagnostic; it neither refutes infinitude nor yields any discovery credit, and the raw statement is unchanged.

**Route A: eventual sign contradiction from the recurrence.** With nonvanishing, failure of infinitely many adjacent sign changes implies eventual constant sign. The known absolute summability and sum c_n=0 do not contradict that: a finite signed prefix may cancel an infinite one-sign tail. Expanding 1/(n+k+1) at large n would require weighted-moment control uniform up to k=n. The available c_n=O(n^-2) does not even guarantee absolute convergence of sum k*c_k. Therefore an interchange/first-moment proof is presently invalid. No numerical extrapolation is substituted.

**Route B: spectral continuation and Landau-type obstruction.** The actual 2026 version of Cloitre arXiv:2505.09645 was retained. Read Theorem 5.1's complete summation-by-parts proof, Remark 5.2 and all Section 6 through its deferral of a spectral expansion. It improves the coefficient bound to O(n^-2), but explicitly leaves the principal-pair expansion as Conjecture 6.1 with a required nonzero amplitude. The transfer and zero-location proofs earlier in that paper were not fully audited here. A zero of the kernel is not a demonstrated nonzero residue for this particular solution. The new size estimate does not give signs.

A possible weaker alternative is to prove that the coefficient Dirichlet series has finite abscissa of convergence and no singularity on the corresponding real boundary, contradicting eventual one-sign coefficients by Landau's theorem. Neither prerequisite was proved: the primary's superexponential lower bound is too weak to force a finite abscissa, and the discrete-to-Volterra bridge is not a full meromorphic continuation theorem for the exact coefficient series. No inference from complex kernel zeros alone is warranted.

**Conditional closing mechanism, not a new result:** an expansion c_n=A*n^-delta*sin(P*log n+phi)+O(n^-delta-eps), with A,P nonzero and eps>0, gives positive and negative subsequences. Choose integers nearest exp((2*pi*j+theta-phi)/P) at positive and negative sine phases; their logarithmic phase errors tend to zero. The error is lower order, so the selected terms eventually have the respective signs. Nonvanishing then gives an adjacent strict sign change between successive opposite-sign terms. This elementary conditional deduction leaves the whole nonzero-amplitude/asymptotic lemma unproved; it is not an unconditional endpoint.

Lean would need the exact recursive sequence and its orthorecursive bridge, analytic estimates or a certified continuation theorem, and the adjacent-sign conclusion. A theorem assuming the spectral conjecture would not solve MathDB. Park, zero credit; no openness or complete successor clearance asserted.

## Rank 3: 343541, odd GP(n,3) minimum coprime number

Read the actual published JIS 24 (2021), Article 21.3.5 definitions in Sections 1–2, the Petersen edge definition, Lemma 1, the beginning and first cases of Lemma 9's GP(n,2) construction/proof, and the complete paragraph preceding Conjectures 11–12 and Conjecture 11. The source matches every odd n>=7 and maximum label 2n+3. Ladders and GP(n,1) are not substitutions. The full multi-case GP(n,2) proof was not audited, and no claim that it proves k=3 is made.

**Route A: sharp parity budget.** The source cites alpha(GP(n,3))=n-2. Conditional on that known independence-number result (its external proof unread here), any labeling with maximum at most 2n+2 has at most n+1 odd labels and therefore needs at least n-1 even labels; even-labeled vertices are independent, impossible. Hence the lower 2n+3 bound is known. At the desired maximum there are n+2 odd labels, so a sharp labeling must use every odd integer through 2n+3 and exactly n-2 even labels. It omits exactly three of the n+1 available even labels. This sharply constrains a uniform construction but does not construct it.

**Route B: affine rails and periodic repair.** The tempting v_i=i,u_i=n+i gives spoke gcd(i,n), and its inner edges at distance three have gcd(n+i,3) away from wraparound. Thus even a prime-n restriction would leave the distance-three obstruction, and composite n brings unbounded spoke divisors. Fixing the wraparound alone cannot solve it. The exact diagnostic lists failures, not counterexamples to existence.

The published GP(n,2) construction uses a period-five ten-vertex block with label increment 12, followed by divisibility repairs. Transferring its base template to k=3 creates new inner pairs: u_5=11 and u_8=22 already share 11. More fundamentally, repeated ten-vertex blocks using a 12-step label span have asymptotic maximum (12/5)n, greater than 2n+3. Bounded changes near finitely many boundaries cannot remove this linear excess. So even successfully repairing those gcds would not establish the sharp k=3 assertion. This eliminates a concrete template-transfer mechanism, not the conjecture.

**Precise remaining lemma:** construct, for every odd n>=7, an injective assignment using all n+2 odd labels and n-2 even labels from [1,2n+3], with coprimality across all outer, inner-distance-three, and spoke edges including wraparound. No density-two periodic template with finite congruence repairs was established. A full Lean packet would additionally need the lower independence bound proved or imported with exact scope, all modular indexing, gcd obligations, distinctness and minimality. Finite label searches would not close the universal endpoint. Park, zero credit.

## Stopped before discovery investment: 379585

The inherited objection concerned lack of a bipartite witness. Bradshaw–Norin–West arXiv:2411.11124 supplies one publicly. Read Section 5's Lemma 5.1 with proof, Theorem 5.2 with its complete construction and concluding proof, and Remark 5.3. Also read Lemma 3.3 and proof, the saturating-set lower-bound ingredient. This is not an abstract-only exclusion.

The public construction joins K_(n,n) to a path on 2^n vertices by a cut-edge, for n an even power of two. It proves p(G)=n+1 and p-hat(G)>n-log2(n)+(log2(n))^2/4. Taking n=256 makes the latter lower bound 264, greater than 257. The graph is bipartite; this directly refutes the exact universal equality, without any transfer to nonbipartite scope. The canonical-labeling characterization and the external exact complete-bipartite parameter used in the proof were not independently rebuilt. No complete dependency audit, published-version audit, new counterexample or Lean work is claimed. Public source dates precede this pass; this route is excluded from new credit.
