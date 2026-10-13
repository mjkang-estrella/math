# I243 — primary literature and exact scope

Only fully read excerpts are retained in this directory. Full retrieved TeX/HTML was used in memory for bounded extraction and provenance hashes; full uninspected transports are not saved. Mathematical source truth at the pinned revision is stipulated, not audited.

## Pinned OpenAI inputs

Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

- [Direct proof excerpts](pinned-direct.tex), from [the pinned primary TeX](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-direct-proof-of-the-complete-Crouzeix-inequality-September-26-2026/build/main.tex). Read `thm:main`; all of Sections 2 and 3 (`lem:faber`, `prop:coefficients`, `lem:resolvent`, `thm:domain` and their proofs); and the statement of `lem:approx`. The exact residual used in I243 is obtained from `eq:diagonal-L2`, `eq:cross-L2`, and the final positive-block comparison. The source proves the complete bound, not four-dimensional equality scalarization.
- [Structural companion excerpts](pinned-structural.tex), from [the pinned primary TeX](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-complete-Crouzeix-theorem-September-23-2026/build/main.tex). Read the coordinate conventions, `lem:conformal-coordinates`, `thm:structural`, `thm:representation`; all of Section 2 including `prop:density` and `prop:extremal`, their proofs and the exact endpoint separation/balance/realization. The companion supplies an attained metric and a common density. Its metric is attached initially to a strictly enclosing analytic domain. I243 does not silently insert equality for W(A) into that domain, and its final route does not need an optimal-metric multiplicity assumption.

These are distinct companion proofs. Neither retained theorem set supplies the asserted equality implication as a stated corollary. The new work is the uniform boundary-slack limit, its rank consequence, and its application to a four-dimensional Hermitian pencil.

## Åhag–Czyż–Virtanen (ACV)

Primary source: [arXiv:2608.27346v3](https://arxiv.org/html/2608.27346v3), *Square Functions, Complete Crouzeix Conjecture in Dimension Three, and the Clouâtre–Ostermann–Ransford conjecture*, version dated 9 September 2026.

Fully read retained extracts:

- [Section 2](acv-s2.txt): finite-dimensional quotient, its exact matrix norms, polynomial density, approximate lifts, adjoints.
- [Section 5](acv-s5.txt): rectangular compression (Lemma 5.1); first variation (Lemma 5.2); minimal extremal with orthogonal base Schmidt spaces (Theorem 5.3); simplicity qualification (Proposition 5.4); exact similarity amplification (Theorem 5.5).
- [Section 7](acv-s7.txt): quotient square functions and full proofs of complete bounds, equality scalarization and diagonalizable estimates in dimension at most three. The equality proof kills products on a cyclic input and uses the three-dimensional monogenic algebra. The obstruction in dimension four is not a missing numerical estimate: (r,s)=(2,2) is genuinely permitted, and columns can have larger cyclic square-zero ideals. I243 accounts for both issues.
- [Theorem 1.3](acv-theorem-1-3.txt): exact scalar-tuple square-function statement. Words alpha range over {1,...,q}^k, and f_alpha is the product in that word. At tau=1/2, equality in the first-order column bound kills all products of length two on a norming input.
- [Section 11](acv-s11.txt): full polynomial equality classification, complete equality through dimension three, inverse-algebra criterion and its limits. In particular Theorem 11.2 classifies *scalar* polynomial equality; Corollary 11.4 does not state the four-dimensional complete implication. I243's final scalar classification is credited to this section, not claimed as new.

I243's quadratic column lemma is a further elementary consequence of the tuple theorem. It does not repeat ACV's three-dimensional proof verbatim: cyclic annihilators of degree up to four and degree-at-most-two polynomial divisibility replace the ambient dimension argument. It is useful auxiliary mathematics, not the substantial contribution by itself.

## Hartz–McCarthy

Primary source: [arXiv:2606.02922v1](https://arxiv.org/html/2606.02922v1), *From Clouâtre–Ostermann–Ransford to Okubo–Ando*.

[Section 4](hartz-mccarthy-s4.txt) was fully read, including Lemma 4.1, its sequence version, proof, and the proof of the main result. The constant-matrix Potapov–Möbius variation and resulting amplified orthogonality are prior art. ACV's finite attained version is the one used here. No first-variation lemma is claimed as I243's contribution.

## Jin

Primary source: [*Rigidity at the Extremal Crouzeix Constant*, v2](https://www.preprints.org/manuscript/202609.0079/v2), posted 15 September 2026.

Read the primary abstract, introduction and Theorem 1 in the primary web rendering. [Theorem 1 excerpt](jin-theorem-1.txt) retains the mathematical statement. It is an all-dimensional **scalar** disk theorem. This is the external dependency turning I243's new scalarization into disk rigidity. Its full proof is not claimed as read in this iteration; ACV Section 11's use and exact formulation were also fully read. The related scalar polynomial classification is likewise external.

## Earlier complete ellipses

The exact BCD Section 5.2 excerpt in the authorized I238 literature file, including Theorem 5.2, Corollary 5.3, proofs and Remark 5.1, was read. It gives the complete two-dimensional ellipse similarity and strictness in the noncircular case. No ellipse estimate or direct-sum example is nominated here. I243 derives a repeated two-dimensional block from a new rank obstruction to four-dimensional complete extremality; the old two-dimensional class is only the terminal reduction.

## Bounded overlap screen

The retained primary statements above were compared with the new result. Three targeted public searches concerned Crouzeix complete equality in dimension four, complete disk rigidity, and extremal positive-block rank. They returned ACV's dimension-three result, Jin's scalar theorem and existing spectral-set work, not a four-dimensional complete equality statement. Search snippets were not used as proof inputs. No I241, I242, other live sibling, shared discovery ledger, or giant history was read.

This establishes a concrete distinction from the primary works inspected. It is not a literature-wide priority certificate. The result remains conditional on the stipulated complete source theorem and its lower operations, and on the explicitly named external scalar-tuple theorem. The main substantial deduction is Theorem 4; the scalar classification and the quadratic-column lemma alone should not be counted as the tenth finding.
