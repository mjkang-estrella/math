# Galois averaging and the mixed-characteristic length estimate

This is preselection feasibility work, not a frozen candidate, contribution rating or independent correctness certification. In particular the scalar all-characteristic IMW conjecture was not frozen and is not claimed solved here. The positive-residue-characteristic calculation below was tested to determine whether a new compatibility operation remained after the actual source and primary contracts were used.

## Contemplated scope and chronology

The exploratory question was the Dutta lower bound for every nonzero complete Noetherian local ring R with residue characteristic p>0 and every finite free complex F in degrees 0,...,d=dim R with finite-length homology and H0(F) nonzero. The numerical target was chi_infty(F)>=e(R) beta0(F), with the characteristic-free localized-Chern definition of chi_infty, no Cohen–Macaulay, reducedness, equidimensionality, grading, field-perfection or finite-Frobenius assumption. beta0 is dim_k H0(k tensor F). No effective constant is sought: the coefficient is one.

All computations preceded selection; no selection or freeze occurred. The early thought was that a normalized-length-to-Euler comparison might be missing. Reading the complete ordinary-norm proof in source193 and then Kurano's actual Theorem1.1 proof removed that proposed obstacle. Kurano was read AFTER the initial deep-entry calculation. The older r10 full rank-isolation body and r82 multiplicity screen were read before final disposition. Their actual mechanisms, not their ratings, control the comparison.

## Actual paid interfaces

At fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, source194 supplies:

* `thm:length-inputs`: for every complete domain D with perfect residue field of positive characteristic, one D-algebra C and one nonnegative additive length lambda work for EVERY system of parameters. The positive Koszul homologies have length zero, and lambda(C/(z))=e((z),D). The stability under uniformly annihilated sums/colimits is part of the contract.
* `thm:complex` and `lem:acyclicity`: supported finite free complexes of length d have lambda-zero higher homology. If their entries lie in (z)^s and the alternating rank is zero, lambda H0>=e((z),D)s^d[b0-A_d(sum b_i)/s]. A_d depends ONLY on d, not on the extension, complex entries or length theory.
* `eq:mixed-deep-entries`: for q>d, a finite normal domain extension D of a complete mixed-characteristic domain R contains q-th roots z_i of a parameter reduction u_i of m_R and satisfies m_R D subset (z)^(q-d)D. The proof uses precisely Heitmann's integral-extension Briancon–Skoda operation with the redundant p^a generator. This containment survives further finite integral extensions.
* `lem:residue-extension`: a flat complete local extension with maximal ideal m_R S and algebraically closed residue field preserves the entire Hilbert–Samuel function.

Source193 `ds:ordinary-norm` is substantially stronger than a positivity statement. If T is a finite local domain over a complete regular normalization A with the same residue field, and a finite group G over A is transitive on geometric fibers, then, for EVERY supported perfect T-complex P,

    sum_g chi_T(g*P) = sum_g chi_C(g*P).

It needs the length identities on the parameters of A. Source194's all-parameter contract supplies these because e(m_A T,T)=rank_A T. The proof establishes finiteness on arbitrary perfect complexes, compares both evaluations on the regular base, and uses `ds:descent` on the invariant norm class. It neither assumes nor asserts invariance of lambda itself under G.

The classical comparison is Kurano, *Test modules to calculate Dutta multiplicities*, J. Algebra236 (2001),216–235, Theorem1.1. The successful body is the author's PostScript at https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano15.ps . Its full pp7–8 proof was read and visually checked. For a Nagata local domain R finite and generically separable over a regular local A, and T its integral closure in ANY finite Galois extension L/Frac A containing Frac R,

    rank_R(T) chi_infty^R(F) = chi_R(F tensor_R T).

This is not an MCM existence theorem. Its proof kills all lower G-invariant Todd components by descent to the regular A, then uses proper covariance of the localized Chern character. The integral closure need not be MCM. Making T larger to include the deep-entry extension is explicitly compatible with the theorem's arbitrary finite Galois L.

## The simultaneous construction

First take R a complete mixed-characteristic domain with algebraically closed residue field k and d>0. Minimize F by splitting contractible free summands, so b_i=beta_i(F). Its alternating rank vanishes since F becomes exact at the generic point. Choose a parameter reduction (u) of m_R, so e((u),R)=e(R), and choose a complete regular Cohen normalization A subset R with residue field k. The two parameter systems need NOT be the same: m_A R need not reduce m_R. This avoids the precise normalization-budget error exhibited in r82.

For each integer q>d, use source194 to construct the finite deep-entry extension D containing z_i=u_i^(1/q). Take a finite Galois closure L of Frac D over Frac A and let T be the integral closure of A in L. Excellence makes it finite; integrality shows it contains D. Completeness and being a domain make T local, and its residue field is k. Its Galois group G acts transitively on geometric fibers over normal A, the standard finite-Galois-normalization contract also used by source193. Put r=rank_R T and P=F tensor_R T.

For every g in G,

    g(m_R)T subset (g(z_1),...,g(z_d))^(q-d)T.

The transformed list is a system of parameters. Finite-module multiplicity and automorphism invariance give, simultaneously for every g,

    q^d e((g z),T) = e((g u),T) = e((u),T) = r e(R).

Neither G nor r is required to be uniformly bounded in q. Take ONE source194 length algebra (C,lambda) for T. It works for all these systems and for the unrelated A-parameter system needed by source193. Every g*P retains length d, ranks b_i and support at the closed point. Apply the complex estimate and acyclicity:

    chi_C(g*P)=lambda H0(g*P tensor_T C)
       >= r e(R) (1-d/q)^d [b0-A_d(sum b_i)/(q-d)].

The same lower bound holds for each g with the SAME error constant. Ordinary length is invariant under the automorphism g, so chi_T(g*P)=chi_T(P). Sum the inequalities, use `ds:ordinary-norm`, and divide by |G|r. Since the residue fields coincide, Kurano's formula then gives

    chi_infty^R(F)
       >= e(R) (1-d/q)^d [b0-A_d(sum b_i)/(q-d)].

The left side is the SAME number for every q, despite changing T, G and C. Let q tend to infinity. This reaches the contemplated coefficient-one bound in the domain/algebraically-closed mixed-characteristic case using the actual compatible contracts. It is not a limit of changing candidate complexes over R. No invariance of the nonnegative length, no flatness of R->T, and no interchange of two unrelated limits is used.

## Passage back to the contemplated ring scope

Source194's residue extension has maximal ideal exactly extended, so minimal ranks, lengths of finite modules, dimension and e(R) are unchanged. The localized-Chern flat-pullback formula preserves chi_infty for this relative-dimension-zero extension: the closed-fiber length is one. The primary Kurano–Roberts author body, *Adams operations, localized Chern characters, and the positivity of Dutta multiplicity in characteristic 0*, opening of Section4, explicitly displays the formula including the general closed-fiber factor and explains its validity beyond finite-type maps. That opening was read; the full characteristic-zero approximation proof was not. Here the source supplies the actual flat complete extension, including imperfect residue fields.

After this extension, top-cycle additivity gives

    chi_infty^R(F)=sum_(dim R/P=d) length(R_P) chi_infty^(R/P)(F tensor R/P),
    e(R)=sum_(dim R/P=d) length(R_P)e(R/P).

This is the definition through the top-dimensional cycle, not the false assertion that ordinary Euler evaluation ignores all lower-dimensional modules. Minimal ranks are the same on each quotient, and localized contractions persist. Each top-dimensional domain quotient has characteristic p or mixed characteristic. For the former the retained-b0 version of source194's Frobenius argument applies; it is explicitly developed in r10 before any r86 work. For the latter use the preceding simultaneous construction. The d=0 case is the equality chi_infty(F)=e(R)b0. This accounts for the positive-residue-characteristic scope, including nonreduced and non-equidimensional rings. It does not assert the residue-characteristic-zero case of IMW8.1.

## Integrated comparison and stopping decision

The point of the calculation is to test the strongest compatible reduction. It succeeds at the alleged obstruction: source194 deepens entries in a finite extension; Kurano allows its Galois closure without changing the normalized Euler target; source194's all-parameter length works for every conjugate and the regular base at once; source193 equates the whole norm sum. Rank and group size cancel exactly. There is no additional transport of individual length values or new numerical functional left to construct.

This is an explicit full-interface comparison, not rejection by calling isolated steps elementary. No residual unpaid compatibility operation was identified in this route. The author therefore submits no nominee and assigns no contribution grade or gate. The all-Betti parameter strengthening is already r10 history and was not repackaged. Nor does this calculation give a lim Ulrich sequence, a finite MCM test module, a nonnegative ordinary Euler theorem over arbitrary R, or the all-characteristic IMW conjecture. Those stronger assertions would require their actual additional interfaces. External sources are not stipulated true, and no worldwide priority claim or independent proof PASS is made.
