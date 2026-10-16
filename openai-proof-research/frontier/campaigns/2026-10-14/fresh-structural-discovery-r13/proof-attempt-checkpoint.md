# Checkpoint 3: full-scope attempts and remaining obstruction

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

## Finite coefficient reduction

Every finite system uses only a finitely generated subgroup C of the torsion-free coefficient group G. If it has a torsion-free solution over C in H_C, then G*_{C}H_C is a torsion-free solution over G. Both vertex groups embed by normal form, and a finite-order element is conjugate into a vertex group, as in checkpoint 2. Conversely a theorem for every G includes finitely generated G. Thus it suffices to settle finitely generated coefficient groups, but not merely finitely presented, recursively presented, solvable, or orderable ones. This is an elementary reduction, not a restricted success.

Rectangular systems can be reduced to square systems by retaining m columns of a nonzero m-by-m minor and setting the other variables to 1. The resulting exponent matrix is nonsingular. This standard reduction is already stated in the pinned source's historical discussion of Gerstenhaber--Rothaus. It is credited, not nominated.

## Attempt A: diagonalize and solve successive equations

Nielsen operations on the variables realize GL_n(Z) on exponent columns while fixing G. Inverting, permuting and multiplying relators realize elementary unimodular row operations and preserve their normal closure. Smith normal form therefore diagonalizes the exponent matrix, with nonzero invariant factors d_i. This says nothing about the actual occurrence of other variables inside commutators. For example x [a,y]^{-1} c^{-1} and y [b,x]^{-1} d^{-1} have identity exponent matrix, although both relators contain both variables. No assertion that this specific system cannot be transformed further is needed or proved.

Forester--Rourke Theorem 1 has an actual layered hypothesis: each new relation involves only previously adjoined variables and its one new variable. In the square unimodular case its diagonal exponents are +/-1, and their relative-asphericity argument propagates torsion-freeness by Proposition 1. Smith normal form of augmentation rows is not such a layering of words. Applying that theorem after matrix diagonalization would silently add an unproved word-level operation. For d_i>1 even the exponent-one hypothesis is absent. TFS allows arbitrary d_i and has not been proved this way.

## Attempt B: the source's planar proof after torsion removal

The pinned Proposition 4.1 pairs EVERY variable slot inside a planar union of signed relator disks. Its boundary components carry coefficients only. The balance equations are

                  sum_i (p_i-m_i) a_ij = 0.

Row independence gives p_i=m_i for every i. The positive and negative arrays of equal size permit the involution J; Theorem 2 then supplies the fixed-space bound. Those are actual hypotheses of the proof, not cosmetic notation.

For a torsion relation v^k in N, the outside word v^k usually has variable slots. The exponent balance is instead

                  sum_i d_i a_ij = k E_j(v).

It need not vanish. The balanced arrays and coefficient-only exceptional boundary of Proposition 4.1 are missing. Substituting a dependent additional relator v=1 fails the rank condition by checkpoint 1. A new punctured-surface or quotient-preservation theorem would have to pay these changes; the existing fixed-space bound alone does not. The example G*P also prevents proving torsion-freeness of the unmodified universal quotient as an unnecessarily strong replacement for TFS.

## Attempt C: residual solvable detection

Let G_r^(0)=G and G_r^(j+1)=ker(G_r^(j)->(G_r^(j))_ab tensor Q). Each quotient G/G_r^(j) has a finite subnormal series with torsion-free abelian factors. Klyachko--Mikheenko--Roman'kov (KMR), arXiv:2303.13240v1, Main theorem and its explicit all-torsion-free-factor corollary, already supply a torsion-free solution over every such quotient. Compose the induced U->H_j with the coefficient quotient. By checkpoint 1 it kills T_omega(U), so

                 G intersect T_omega(U) subset intersection_j G_r^(j).

If this intersection is trivial, this proves TFS for G, but this is a standard residual closure of the KMR operation (their Proposition 2 supplies the quasivariety framework). No new substantial result is claimed, and this is not substituted for the frozen all-group assertion. For a perfect torsion-free G the right side is G itself, so this argument supplies no detection.

A perfect torsion-free group exists without any appeal to the pinned Artin family. Let F_j be free on 2^(j+1) letters and embed F_j in F_{j+1} by sending its l-th generator to the commutator of the (2l-1)-st and 2l-th new generators. These maps are injective: powers of each cyclically reduced commutator remain reduced, and consecutive distinct generator blocks use disjoint alphabets, so a nonempty reduced word cannot vanish. Their direct limit L is nontrivial and torsion free, since each element and any finite power relation occur in a free stage. Every stage generator becomes a commutator at the next stage, so L=[L,L]. Thus every map from L to a nilpotent group is trivial: its image is both perfect and nilpotent, and a perfect group's lower central series is constant, which is incompatible with nontrivial nilpotence.

Consequently a blanket embedding of all torsion-free groups into a separated, integer-degree Magnus group (whose degree truncations are nilpotent) is false. This observation does not rule out other filtered constructions, the more general real-degree monoids in Ramirez-Cote--Wise, or solving finite systems over L. Indeed finite coefficient subgroups of L lie in a free stage. It is a limitation of that particular global completion shortcut, not a TFS counterexample.

Ramirez-Cote--Wise Theorems 9--10 already solve square nonsingular systems for groups EMBEDDED into their specified 1+K power-series groups, inverting det(A) in the scalar ring. Their embedding assumption cannot be dropped just by invoking nonsingularity. KMR's Main theorem with K equal to the class of all torsion-free groups would also be circular: its premise that K is already a Howie quasivariety is precisely the unsolved assertion here.

## What would finish the target

For every original nonsingular system, prove G intersect T_s(U)=1 for every finite s, or construct one system for which that intersection is nontrivial. Neither has been done. All reductions preserve the original quantifiers; none supplies the coefficient-preserving dependent-relator step. The known constructions and explicit torsion tower above are technical support. No complete proof or genuine counterexample to full TFS is proposed.
