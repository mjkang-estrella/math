# Checkpoint: what the recovered Brodsky–Howie paper actually pays

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Primary source: S. D. Brodsky and J. Howie, *The universal torsion-free image
of a group*, Israel J. Math. 98 (1997), 209–228,
DOI 10.1007/BF02937335. Full publisher PDF obtained, retained privately,
and read throughout: all 803 extracted lines, printed pp. 209–228.
The printed hat over G is frequently lost by pdftotext: in the conclusions
below it is the universal torsion-free IMAGE bar(G), not G itself, that is
asserted locally indicable. A rendered first theorem page was also checked.

Let rho(G) be the intersection of kernels of maps to torsion-free groups,
and bar(G)=G/rho(G). The introduction defines this radical. Its operation
is the same radical credited in r13 and Chiodo; it is not new here.

The exact small-presentation interfaces are:

* Lemma 1.1: for a one-relator group G, bar(G) is locally indicable.
  Its proof replaces a proper-power relator s^m by s and uses the
  torsion-free one-relator local-indicability theorem for the root quotient.
* Theorem 1.2: for a two-relator group, if one relator has length at most
  four, bar(G) is locally indicable.
* Theorem 1.3: for a two-relator group, lengths five and at most eight
  suffice for the same conclusion.
* Theorem 1.4: at most five relators, each of length at most three,
  suffice. Corollary 1.5 expresses this by complexity at most five, where
  complexity is the sum of length(r)-2 over relators other than powers
  of generators.

Lengths refer to the ordinary displayed generators, not just unknown-variable
exponent rank in an arbitrary relative presentation. The proof reduces the
short presentations by elimination and HNN/one-relator arguments, and in
some small final cases appeals to coset enumeration. Reading those statements
does not independently certify their historical computations, and none ran.

The application, Theorem 1.6, takes torsion-free factors A,B and a cyclically
reduced w∈A*B of length at least two. If a∈A has an expression as a product
of at most FOUR conjugates of w or w^{-1}, then a=1. It is not an arbitrary
finite-system theorem, a bound for every radical stage, or an assertion that
every torsion-free coefficient factor embeds in the universal torsion-free
image of a nonsingular relative presentation.

Here is the proof's actual use of the radical. A minimal nontrivial
coefficient witness gives a connected spherical picture with n vertices.
The face counts obey Σ(k-2)F_k=2n-4. Abstract coefficient groups A0,B0
are presented by the region relations of this picture. Their maps to the
original torsion-free A,B factor through bar(A0),bar(B0). When n≤4,
the complexity bound puts these images in the small-presentation theorem.
Local-indicability results then rule out that picture. The radical is applied
to ABSTRACT COEFFICIENT GROUPS before mapping into A,B, rather than assumed
to preserve A or B inside an arbitrary relator quotient.

For arbitrary n the bound is 2n-4, with no uniform ceiling of five. Full
row rank does not bound n, relator lengths, or these region presentations.
No new reduction establishing the required smallness for a finite radical
certificate has been proved. In particular, substituting U for G in
Corollary 1.5 would require an ordinary small presentation for U, and even
local indicability of bar(U) would not establish G↪bar(U). That injection
is the target operation, not a conclusion of the corollary.

The paper's sharpness examples explicitly include nonindicable torsion-free
groups beyond its thresholds. We do not use their manifold identifications
as unchecked new deductions. The separate Higman-group normal-form argument
in the universal-coefficient checkpoint supplies the test group properties
we actually use without those identifications.

The recovered primary source thus resolves the retrieval uncertainty and
locates the exact paid operation. It supplies no omitted full TFS proof.
No worldwide priority or current-open-status claim is made.
