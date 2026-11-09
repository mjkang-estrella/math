# A full spectral certificate for MathDB362146

Status: complete Lean proof of both parts of the question, for every field and finite matrix index set. One distinct MathDB question. The source's characteristic-zero and d>1 cases follow by specialization.

Question: [MathDB362146](https://mathdb.com/p/362146/the-eigenvalue-conjecture-for-permutation-like-matrices), UUID `67a04085-8dd9-4158-a8b4-f7b2324c744d`. Primary source: Steven Robert Lippold, *Permutation-Like Matrices*, [arXiv:2403.02478v1](https://arxiv.org/html/2403.02478v1), Definition 2.1 and Conjecture 5.2. The exact API record and versioned primary HTML are saved in `../sources/`.

## Exact theorem

A permutation-like matrix has entries zero or one and exactly one entry equal to one in each column. Its eigenvalues are zero or roots of unity. Zero is an eigenvalue if and only if the matrix is not a permutation matrix. The identity is itself a permutation matrix, so excluding it separately is redundant; `exact_mathdb_conclusion` also prints that exclusion explicitly.

The Lean theorem uses mathlib's actual `Module.End.HasEigenvalue A.toLin' μ`. A separately checked equivalence relates this to the ordinary nonzero-vector equation `A *ᵥ v = μ • v`. `IsPermutationMatrix` means exactly one unit entry per row as well as per column, with every other entry zero.

## Full proof

Write the matrix as T_f, where f maps each column index to the row of its unique 1. Direct multiplication gives T_f T_g = T_(f∘g), hence T_f^n = T_(f^n). Since the set of functions on a finite set is finite, there are integers p<q with f^p=f^q. Therefore T_f^p=T_f^q.

If T_f v=μv and v is nonzero, then T_f^n v=μ^n v. Choosing a nonzero coordinate yields μ^p=μ^q. For μ≠0, cancellation gives μ^(q-p)=1, with q-p>0. This proves the first claim without Jordan form, algebraic closure, a spectral-radius assumption, or a restriction to eventual row matrices.

If f fails to be injective, choose i≠j with f(i)=f(j). Then the nonzero vector e_i−e_j is killed by T_f. If f is injective, finiteness makes f bijective and T_(f⁻¹) T_f=I, so there is no nonzero kernel vector. Finally, f is injective exactly when T_f also has one 1 per row, which is precisely the permutation-matrix condition. All these steps are in the Lean source.

## Source comparison and limits

The primary paper already proves closure under multiplication (Proposition 2.1), the root-of-unity assertion for d=2,3 (Corollary 4.5) and for pre-row matrices (Proposition 4.2), and the zero-eigenvalue criterion (Proposition 4.4 and Corollary 4.7). Those are credited antecedents, not new results of this lane. Its Conjecture 5.2 asks for the remaining all-dimensional spectral assertion. The finite-transformation-semigroup argument supplies it directly and is elementary; no worldwide novelty or priority claim is made.

At retrieval, MathDB reports zero replies and zero formalizations for this record. A bounded web search for the title, arXiv identifier and root-of-unity assertion found the primary source and no separate general proof; that is not an exhaustive literature search. A repository Markdown/Lean search outside this lane found no occurrence of this question's ID, title or distinctive terminology. This is new to the audited project corpus, subject to those search limits.

## Validation

Run `python3 formal/rebuild.py`. The build script follows the existing premagic certificate's pattern: Lean 4.34.1, pinned mathlib and dependency revisions, fresh local objects, warnings as errors, complete type/axiom transcript, and only standard kernel axioms. It does not install or alter dependencies. Compiler and prebuilt dependency objects remain trusted.

Paper source is in `paper/main.tex`; no PDF was generated. Original local code is MIT and original prose CC BY 4.0. Third-party source rights are unchanged.
