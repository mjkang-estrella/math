# PREFREEZE: endpoint completion and the finite-list interface

This continues the concrete construction in 01-prefreeze-construction.md. It is neither a frozen theorem nor an author proof for submission. All actual Source324 proofs are stipulated true. The question investigated is a global Lipschitz correction lift into a Schur space, not a revision of old S88 or a claim that this question is globally open or impossible.

## 1. A concrete analytic model prevents an unjustified Schur inference

The preceding construction produces, for each normalized weakly null sequence, a fixed compatible detector family with a bounded evaluation map into ell_q for EVERY q=1+1/k>1. Its constants depend on q. That information cannot be upgraded to a bounded map into ell1 by taking q down to 1.

Here is a fully explicit model for this failure of the analytic interface. On c00 define

    ||a||_W=sum_(k≥1)2^-k ||a||_(p_k), p_k=1+1/k,

and complete. The unit vectors e_i have norm1, and each coordinate embedding into ell_(p_k) is bounded by 2^k. For ANY finite subset H of n indices and ANY signs,

    ||sum_(i in H) epsilon_i e_i||_W
      =phi(n):=sum_k 2^-k n^(1/p_k),
    phi(n)/n=sum_k 2^-k n^(-1/(k+1)) →0.

The last limit follows by first choosing a finite k-head with remaining weight small, then sending n to infinity in that finite head. For a bounded functional f on W, if |f(e_i)|≥epsilon on infinitely many indices, choose signs matching these values on n of them. Then epsilon n≤||f||phi(n), contradicting the limit. Thus e_i is normalized weakly null. W is not Schur despite all the bounded ell_(1+1/k) coordinate evaluation maps and an outer ell1 norm. This is a counterexample only to the proposed abstract analytic inference, NOT to any Source324 theorem and NOT a realization of W inside Z_1.

The example also rules out relying on slower positive weights: for any positive summable weights with sum1, the same dominated finite-head argument gives phi(n)=o(n). Exponents staying strictly above1 cannot supply the endpoint bound solely by summable reweighting.

## 2. Adding the endpoint without damaging the nonlinear identity

Let e=(L,C) range over the source class/integer-bound pairs, forgetting p. Define

    tau_e(m)=sup {sum_(u in A)|u(m)| : A is a finite admissible list
                  from L with common signed Lipschitz bound C}.

Use the exact source notion of admissibility. Lists may repeat functions or labels. For each pair e set gamma_e=sum_(d projecting to e) beta_d. Then gamma_e>0 and sum_e gamma_e C_e=1. Define

    N_end(m)=sum_e gamma_e tau_e(m).

For point differences tau_e(delta_s-delta_t)≤C_e||s-t||, so N_end is finite on finite molecules and the point map is 1-Lipschitz. It is a genuine seminorm by Minkowski for ell1, not a quasi-norm obtained by illicitly putting p<1 in the old formula. Its kernel is still the common zero-test kernel: tau_e(m)=0 for all e iff every individual generated test pairs to zero, iff every old sigma_d does.

Complete the quotient to Z_end. Realize it linearly in the ell1 sum of the tau_e quotient completions, exactly as in Section2 of the preceding note. This proves the completed formula and bounded extension of all admissible list maps. Since sigma_d≤tau_e for the corresponding e,

    N_1(m)≤N_end(m).

The identity extends continuously from Z_end into Z_1. It is injective: if its image is zero, all individual test pairings are zero; the exact completed list formula makes every tau_e zero, and the exact norm formula then gives z=0. Its range is dense; no inverse bound is inferred.

Singleton base correction tests in e_0=(T_1,C_0) give

    ||Q_end m||_U≤tau_(e_0)(m)≤gamma_(e_0)^-1 N_end(m).

Thus Q_end extends to U. The point map zeta_end is 1-Lipschitz; radial K_end has Lip≤3, and Q_end K_end=g-P exactly. The unchanged global source g and its entire onto proof give an actual bi-Lipschitz bijection

    F_end(b,t)=b+K_end(t,Q_end b)

from Z_end⊕∞c0 onto Z_end, with the same explicit inverse formula and constants from the source lemma, using q_end≤gamma_(e_0)^-1. This is a completed, full-domain nonlinear construction, not an approximation, a finite-stage claim, or an assumption that Q_end is onto.

However, an injective dense map from Z_end into Z_1 does NOT transfer no-c0: a bounded injection need not be bounded below on a hypothetical c0 copy. The same warning applies to the original j:Z_1→Z; this is why the preceding note actually reproved its obstruction. No no-c0 or Schur assertion for Z_end is made here.

## 3. What the endpoint does pay, with exact quantifiers

Every infinite sequence (v_j) from one class L, all of whose finite lists are admissible with bound C, now defines a bounded linear map

    T:Z_end→ell1,  Tz=(v_j(z))_j,  ||T||≤gamma_(L,C)^-1.

This follows directly from the finite list formula and monotone convergence. Consequently, on ANY weakly null sequence z_i, ||Tz_i||_1→0 by the Schur property of ell1. There cannot be such a compatible detector sequence with |v_i(z_i)| bounded below.

Also, for a normalized weakly null sequence z_i in Z_end, the outer ell1 gliding-hump proof still supplies one fixed pair e=(L,C) for which tau_e(z_i)≥a>0 on a subsequence. Thus there are finite admissible lists A_i in this fixed class with

    sum_(u in A_i)|u(z_i)|≥a/2.                         (B)

The lists are individually compatible with the SAME C. Their lengths are unbounded in the unresolved case. This is the precise residual after the endpoint and nonlinear lift are constructed, not merely a named Schur-property gap.

## 4. Why the source single-detector selection does not yet settle (B)

For each individual completed vector z, the monotone equality

    tau_e(z)=sup_(k≥1) sigma_(L,C,1+1/k)(z)

is exact. Indeed the supremum over finite lists commutes with the supremum over k, and a finite ell_p norm increases to its ell1 norm. But for a sequence z_i, (B) only permits an exponent k_i depending on i. It does NOT supply a fixed k with sigma_(L,C,1+1/k)(z_i) bounded below on a subsequence.

The elementary array x^(N)=(1/N,...,1/N) of length N has ell1 norm1 but ell_p norm N^(1/p-1)→0 for every fixed p>1, and largest entry1/N. Thus source interpolation cannot extract one test with a fixed nonzero pairing from (B). This array is an exact failure of an estimate between scalar list norms, not an asserted family of realized molecules in Z_end.

Appending a singleton G-operation per detector is valid only after selecting that detector. For a whole list one can individually choose modifications so that the total pairing error is below a/4: for each fixed finite list A_i with n_i members choose errors less than a/(4n_i), applying the fixed-vector convergence within enlarged source classes. This closes the finite-list approximation step, including growing n_i. It does NOT close compatibility of the union of all modified lists. The needed global increment sum is over every list element across all selected i, not just over one scalar test per i.

In the source distinct-band argument, each selected scalar test has one shrinking cylindrical support and one plateau for all later scalar supports. An arbitrary admissible list can contain arbitrarily many separated cylinders, repeated labels and different bands simultaneously. Their union need not concentrate at one finite-coordinate tag. The scalar repeated-label expansion has at most 2^(2h) terms PER TEST; with n_i tests this gives n_i 2^(2h) terms. Discarding fixed-term pairings uses weak nullity for a FIXED finite set of tests. It gives no common control for a changing collection of n_i fixed-ingredient terms whose cardinalities grow. Selecting one term can divide detection by n_i. The explicit n_i error correction above does not restore that lost lower bound.

Tail separation alone also does not solve all panels: one can separate panels whose entire supports force a COMMON positive tail threshold beyond M_i→infinity, but an individually admissible list need not have that property. Treating its sum H_i=sum sign(u(z_i))u as one C-Lipschitz test loses its representing label and the source finite-support/ordered-budget hypotheses. No rule in T_h or V_h says this H_i is a member of a fixed enlarged class independent of n_i.

## 5. A sufficient finite-list operation, stated exactly as an unpaid obligation

For a weakly null sequence z_i in Z_end with r≤||z_i||≤M and admissible A_i in a fixed (L,C) satisfying (B), one sufficient missing operation would give:

- an infinite subsequence i_k;
- one source class L', one integer C', and delta'>0;
- finite lists V_k in L', chosen after the corresponding z_(i_k),
- sum_(v in V_k)|v(z_(i_k))|≥delta' for each k;
- for EVERY finite K and EVERY choice of signs on EVERY list element,
  Lip(sum_(k in K)sum_(v in V_k) epsilon_(k,v)v)≤C'.

Indexing by (k,v) retains repetitions, as in the source norm. The union then defines the bounded ell1 evaluator from Section3, whose norm on z_(i_k) is at least delta'. Its norm must instead tend to zero, a contradiction. This would prove that the explicit Z_end is Schur and would finish its already-constructed global absorption map. Neither this finite-list operation nor an alternate Schur proof is established. No necessity or impossibility claim about that operation is made.

The work has gone beyond just restating that desired operation: the completed endpoint norm, its injective maps, exact correction lift, full onto nonlinear bijection, fixed-pair localization, exponent obstruction, finite-list modification estimate, and the failure of the naive union-support argument are all given above.

## 6. Strongest actual primary constructions and their exact applicability

Kalton2004 Lemmas4.1–4.5, Theorem4.6, Propositions5.1–5.2 were read in their actual published-style PDF. The annular ell1 decomposition and Lipschitz cutoffs are available operations. The Schur proof uses norming little-Lipschitz functions for a nontrivial gauge omega, with omega(t)/t→infinity as t→0. It constructs additive norm growth, then an ell1 subsequence of a hypothetical normalized weakly null sequence. Its triangular uniform equivalence controls distances by 3omega. Since omega(t)/t is unbounded near0, that control does not supply the all-scale Lipschitz bound required here. Merely replacing zeta_end by the snowflaked free point map would sacrifice exactly the metric interface QK=g-P with a globally Lipschitz K. No audit of that primary proof or of the stipulated sources is involved.

ANPPv3 Theorem2.3 and the FULL displayed proof in Section3 were read. They localize weakly precompact sets in the FULL free space using support-preserving multiplier preadjoints, repeated compact-set approximation and a limiting operator. They do not automatically define bounded operators on a selected-test quotient completion. For a multiplier h to descend here, one would need, for instance, an inequality controlling the pullbacks of every admissible list in the endpoint norm; full Lipschitz estimates alone control the full free norm, which is generally stronger. Thus tightness cannot simply be quoted for Z_end. The separate KPv2 Main Theorem/Theorem9 proof was read: its smooth derivative products construct weakly unconditionally Cauchy dual tests on the full free space over a compact subset of a superreflexive Banach space. Neither its ambient superreflexive hypothesis nor its full-free dual norm is the present c0 selected-test setting. The cited smooth approximation and renorming inputs were not independently reproved.

GK2003 Theorem3.1 was read with its actual cube-integral lifting proof, as were Proposition2.8, Theorem2.12 and Corollaries3.2–3.4. There is a particularly concrete obstruction to the maximal enlargement that takes ALL Lipschitz scalar tests with a uniform dual bound. On B, the usual free molecule norm is

    ||m||_F=sup_(Lip(f)≤1)|f(m)|.

Every selected admissible-list norm above is ≤||m||_F (apply signs and then the full free norm), so N_end≤||m||_F. If the enlargement also made every 1-Lipschitz f a uniformly bounded dual functional with common constant A, it would give ||m||_F≤A N_end. The completion would be linearly isomorphic to F(B).

But F(B) already contains a linear isometric copy of D, hence c0. To see the ball-supported version explicitly, choose a linearly independent dense-spanning sequence x_n in D with sum||x_n||≤1. The compact cube K={sum t_n x_n:0≤t_n≤1} lies in B. The GK integral vectors phi_n=int[delta(x_n+S_n(t))-delta(S_n(t))] use only points of K. Its norm-one linear lifting R:D→F(D) therefore takes values in F(B), and beta R=Id. Since F(B) embeds isometrically in F(D), R remains an isometry into F(B). Thus the maximal full-Lipschitz enlargement cannot yield the desired Schur/no-c0 obstruction. This is a genuine failure of that specified enlargement, not a proof that intermediate selected families cannot work.

Sari2026v2 Sections3–6 were read through the complete retraction, edge-basis, annular dual-target and sharp G_2 obstruction proofs. Uniform 2-Lipschitz finite-height retractions and the ell1 annular assembly operate on the integer grid G, a fixed-separated metric space. Rounding c0 to G allows an additive small-distance error; rescaling a grid leaves a fixed positive mesh in each construction. A Lipschitz map from connected c0 into a fixed discrete grid must be constant. Accordingly these actual coarse constructions do not replace the missing continuous global correction lift with a dual or Schur target. Its Corollary6 uses Aliaga–Medina results by citation; those deeper proofs were not independently read or used here.

The baseline Source324 Hilbert graph construction uses the FULL F(M) for a Hilbert M and gets complete continuity only for q, not Schur for the domain. GK already embeds Hilbert space linearly into F(M). Its graph obstruction must use whole Hilbert blocks and WSC. Substituting that full free norm for the companion's selected norm would erase the scalar no-c0 mechanism as above. Conversely replacing the Hilbert domain by c0 does not preserve the superreflexive WSC theorem. These are actual compatibility checks between both canonical constructions, not a rejection of their stipulated conclusions.

## 7. Outcome of this reduction

The developed route has two explicit completions. Z_1 supports the full global source absorption and the extended weakly-null detector calculation, but its new calculations are assembled from source selector operations and elementary ell1/gliding-hump/exponent estimates. They are retained as prefreeze work, not offered as a weaker finding. Z_end supports the global absorption with an exact endpoint evaluator; its Schur/no-c0 conclusion is unproved at the finite-list interface above. No viable full theorem with a closed identifiable nonroutine bridge has emerged. No theorem is frozen and no author-proof nominee is submitted. This is PREFREEZE/no nominee with a concrete reduction, not exhaustion, a worldwide novelty claim, or an impossibility claim for neighboring targets.
