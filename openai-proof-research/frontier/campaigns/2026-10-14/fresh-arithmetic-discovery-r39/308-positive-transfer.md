# 308 positive transfer analysis (not a substantial nomination)

## Status and chronology
The possible all-height/all-finite-thickening statement was explored before any freeze. The operation comparison now indicates a classical finite de Rham construction applied to the source's explicit finite-cell model. It is retained as a technical derivation, not a new candidate, not an independently reviewed theorem and not a count. No narrower substitute is selected. The display below spells out why the idea is more concrete than an unsupported realization promise, while identifying the exact category interface that a future proof user must check.

Write I=(p,v1,...,vn). The intended output would be a finite ordinary p-local spectrum with BP-homology BP_*/I^k for each fixed pair n,k, with p depending on both. A fixed prime for all n or all k, an infinite compatible tower at one prime, and multiplicative structures at the prime were never claimed.

## Finite model
Use the stipulated source's Proposition found:koszul-realization and norm:construction. Set A=h_Omega(1), and B=A[e0,...,en], with odd chain-degree-one generators of weights wi and differential de_i=b_i in the earlier generators. Put m=n+1. Its relative de Rham algebra, in homological total degree, has even variables t_i of weight wi. Its finite Hodge quotient is

    D_k(B/A)=A[e0,...,en,t0,...,tn]/(t0,...,tn)^k.

Let delta be the degree-minus-one derivation with delta(e_i)=t_i, delta(t_i)=0, delta(A)=0. Extend the original differential by d(t_i)=-delta(b_i). Then d delta + delta d=0 and delta^2=0 on generators, hence everywhere. The total differential D=d+delta satisfies D^2=0. Thus

    D(e_i)=b_i+t_i,       D(t_i)=-delta(b_i).

The ideal of t-monomials of total degree at least k is preserved. There are exactly 2^m binomial(m+k-1,m) basis monomials over A. For a finite-cell order, list indices decreasingly; at index i first compare the total number of e_i and t_i, then the e_i count. Replacing e_i by t_i decreases the second count; replacing e_i by b_i or t_i by -delta(b_i) decreases the total count at i and introduces only smaller indices. Repeated exterior generators vanish. The differential is therefore triangular on a finite ordered basis, even if the coefficients of b_i have arbitrary chain degrees. This gives a finite-cell A-module, not just an abstract perfect object.

All Hodge filtration subquotients are finite-cell by the same argument. The source finite-cell equivalence realizes these objects, their maps and the unit as finite constructions in its ordinary spectral ultraproduct.

## Why base change is manageable
Put M=h_Omega([(MU_(p))_p]). Source real:hurewicz says that at the ith stage the image of b_i is a scalar unit times the MU coefficient x_i modulo the preceding x_j. Choose cycle representatives x_i in M. Inductively the difference b_i-u_i*x_i is an exact degree-zero cycle in the preceding cell algebra. Choose a degree-one primitive h_i and replace the new generator by

    e'_i=u_i^(-1)(e_i-h_i).

This is a triangular coordinate change with unit diagonal. Induction identifies the base-changed cell algebra with the regular Koszul algebra M[e'_i], de'_i=x_i. Relative de Rham is functorial under this coordinate change; t'_i=delta(e'_i) is linear in the old t-variables, and the Hodge filtration is preserved. This uses actual chosen primitives, not an inference that isomorphic homology algebras are formal.

On the resulting model D(e'_i)=x_i+t'_i and D(t'_i)=0. It is the Koszul complex for x_i+t'_i over M[t']/(t')^k. The familiar regular-quotient calculation identifies its homology with H(M)/(x0,...,xn)^k. One can avoid assuming formality of M by base-changing the finite free universal calculation over Q[X0,...,Xn]: the ordinary Koszul complex on X_i+t_i resolves Q[X]/(X)^k. Regularity of the x_i on H(M) makes the derived base change exact, first for the quotient by (X), then for all powers by their finite filtration with free Q[X]/(X)-layers. These are classical regular-sequence/derived-de-Rham operations.

## The all-degrees descent issue
An isomorphism of weightwise ultraproduct homology alone is insufficient: it would not justify intersecting infinitely many large prime sets. The finite data that can instead be retained are as follows.

1. The finite filtration F^0 D_k ⊃ ... ⊃ F^k D_k=0, its cofiber sequences, and its unit.
2. After MU base change, each graded layer is a finite sum of shifts of M⊗Y_{n+1}. Retain those equivalences with inverse maps and inverse homotopies. This uses finite diagrams of MU-module maps; the finite-cell generator/cofiber proof of the source's comparison applies also to such maps with arbitrary target.
3. For each multi-index alpha with |alpha|<k, retain the lift of x^alpha times the unit into F^{|alpha|}. On its graded layer the image is the basis element (-t')^alpha times the quotient unit. Retain these finitely many equalities and their specified homotopies.
4. For each |alpha|=k, retain the nullhomotopy of x^alpha times the unit in the base-changed total object.

At a common prime these finite data coexist with the source's identification MU_*Y=MU_*/I. All shifts in the graded layers are even. Descending induction through the finite filtration therefore gives short exact sequences in even homology and zero odd homology. The retained monomial lifts generate every layer over MU_*/I, so the unit surjects in every degree. The degree-k monomial relations make it factor through MU_*/I^k. The map identifies the associated graded with I^j/I^(j+1), and hence is an isomorphism by finite induction. This is a finite filtered-module argument, not a compactness argument over infinitely many degrees. Base-changing the same finite diagrams to BP gives the corresponding calculation there, using the source equality between the ideals generated by the x_i images and (p,v1,...,vn). The sphere unit then fixes the quotient comodule structure.

The interface in item2 should be stated explicitly in any formal theorem proof: one works with the ultraproduct of primewise MU-module categories, or equivalently checks each map with finite free MU-module source and then extends by its finite cell filtration. An arbitrary diagram of module objects in an ultraproduct is not being asserted to descend.

## Operation-level attribution and decision
Bhatt, Completions and derived de Rham cohomology, arXiv1207.6193v1, introduction (actual body lines64–69), explicitly gives the regular-ideal Hodge-truncation/I-adic-truncation identification and credits Illusie's lci comparison. The polynomial model above is that standard operation.

Wüthrich, Infinitesimal thickenings of Morava K-theories, arXiv math/0607110v2, introduction and Theorem1.1 (actual body lines41–83), constructs ideal-power towers for regular pairs over an even commutative ring spectrum. The output is structured module/algebra spectra over that ground ring; it is not automatically an ordinary finite sphere-based realization. His earlier I-adic towers in topology, math/0411409v1, definitions2.1–2.3, specifies the ambient R,T,F relationships. Only these stated ranges were read here, not his full proof.

The pinned source supplies the special rational graded model, the finite-cell Morita equivalence, compatible odd-cell tower, MU coefficient detection and finite-diagram descent. The proposed residual consists of applying the classical finite de Rham model and retaining a finite list of filtration bases and relations. The ordinary-finite output is different from a mere MU-module, but this distinction alone does not constitute a substantial new operation. The author therefore does not nominate this transfer. No global novelty or independently checked full-proof status is asserted.
