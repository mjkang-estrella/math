# Proof and evidence boundaries

DRAFT, prepared with OpenAI Codex assistance; no fabricated human authors or affiliations. Submitted to root for review, not accepted. Only MathDB 347230 is the principal result; 347231 and Lemma 5.11/36 are remarks.

## Exact claim

Over Q, let V_n be the free vector space on length-n words in a,b, with reversal star. Let Delta delete one letter at each position. Use Ehrenborg-Readdy Definition 9.1, with M_(1,2,2)(u,v)=uav and M_(2,1,2)(u,v)=vbu, and the alternating deletion recursion printed in manuscript.ms. Let I_2(w)=w+w*+sum_(p,q in Delta(w)) M(p*,q). Then ker(I_2|V_5) has dimension 13, whereas dim A_5=12, where A_n is the reversal-antisymmetric subspace. In particular, Hetyei's Conjecture 5.14/39, understood as in the root ruling, is false.

## Certificate proof

The complete certificate is equation (4) of manuscript.md and computations/results.json, transcribed independently in scripts/recompute.py. It has 20 nonzero coefficients and is homogeneous of degree 5. Reversal preserves each coefficient and the coefficient of aaaba is 1. Its image is zero: computations/certificate-contributions.tsv records each of the 20 signed word images in all 32 degree-five output coordinates. Every column sum is zero. This is finite exact computation using the source recursion, not a presumed structural formula. The bounded recursion is exhaustive: every step deletes a letter, so an index above |p|+|q|+2 gives no term. The verification uses 1536 expanded signed unit contributions with multiplicity, not the unweighted 1280. Thus a nonzero symmetric element lies in the kernel and cannot be antisymmetric over Q. This alone refutes the conjecture.

## Dimension and poset checks

For degrees 1 through 7, scripts/recompute.py constructs the full integer operator matrices and performs exact Fraction Gauss-Jordan elimination. Matrix files retain word orders, input matrix, pivot steps and rational reduced matrix. Nullities are 0,1,2,6,13,30,63; antisymmetric dimensions are 0,1,2,6,12,28,56. Reversal-fixed words number 2^ceil(n/2), giving dim A_n=(2^n-2^ceil(n/2))/2. The ER symmetry gives I_2(w*)=I_2(w); this inclusion is also checked on every matrix column. Rank 19 in degree 5 proves the claimed dimension 13.

For D(n,S), every internal rank has one element, or two if in S, with complete comparability across ranks. Its flag coordinate f_T is 2^|S intersect T|. The flag matrix is the tensor power of [[1,1],[1,2]], whose determinant is 1. The substitution a -> a-b is invertible, so the indices span V_n. The script directly enumerates every component [[x,x],[0-hat,1-hat]] and its proper chains for every doubled chain through degree 5, obtaining the same total ab-index as I_2. At degree 5 this checks the entire operator on a basis. No single-poset realization of the certificate is claimed.

## Source interpretation and formal result

The source's ubv base case conflicts with ER Definition 9.1, equation (5.1), and Corollary 5.8; it gives the different artefact I_2(ab-ba)=2ab-2ba. The printed V_(n+1) codomain also conflicts with degree preservation. The root ruling explicitly adopts the ER reading and awards nothing for these misprints or for 347231 separately.

The preserved source-only.zip has SHA-256 c96ee05e7799bca2aa7a35961e931185425ed44c8efd7160c73452d8a8d6054c. Its exact endpoint is `Hetyei347230.kernel_conjecture_false : ¬ Hetyei347230.KernelConjecture`. Its proved range lemma, rational bridge, and degree-two control are described on manuscript page 5 and in evidence/hetyei-formal-r1/STATEMENT-CORRESPONDENCE.md. The kernel refutation is formalized; the rank table, general Corollary 5.8 proof, poset enumeration, and companion remark are not formalized in that packet.

Root's supplied replay-result.json reports strict PASS and allowed axioms only; registry-refresh.json reports CLEAN subject to path-screen limitations. No Lean tooling was executed in this lane. The packet was copied byte-identically, safely extracted, and its internal source manifest verified. See receipts. Formal and independent review provenance is preserved as evidence, rather than presented as a fresh replay by this lane. All acceptance, significance and novelty decisions remain with root.
