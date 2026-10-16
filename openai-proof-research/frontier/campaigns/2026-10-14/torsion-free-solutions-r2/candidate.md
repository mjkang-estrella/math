# Unchanged TFS, focused second attempt

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party materials are private
and retain their original rights.

**UNRESOLVED_FULL_TFS.** No full proof or counterexample was found. This report
does not nominate the supporting deductions, claim an independent PASS,
increase the count, or replace TFS by a subclass. The campaign remains **4/10**.

## Frozen assertion and exact missing operation

For every torsion-free group G, every finite 1≤m≤n, and every ordered system
w_1,...,w_m∈G*F_n whose exponent matrix has rational row rank m, TFS asks
for a torsion-free group H embedding G and simultaneous values of all unknowns
at which all w_i are 1. Arbitrary cardinalities, ineffective coefficient
groups, all words and all nonzero invariant factors remain included.
`original-scope.md` is copied byte-identically from r13, SHA256
`be98807412ea2c5fc4a2b71f44ce63ee3f46bc21d4c6522185a56a92b46f9c06`.

Let E=G*F_n, N=<<w_i>> and U=E/N. The stipulated Theorem 1 of
*Nonsingular systems of equations over arbitrary groups*, openai/math
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, embeds G in U. Its actual
interface supplies no torsion-free image. Its companion Theorem 1.1 and
Corollary 1.2 supply unrestricted unimodular injectivity and one-relator
nontriviality, respectively. No upstream truth audit was attempted.

For clarity, the standard radical equivalence remains the full gap. Set
T_0=1 and T_{j+1}=<<u:u^k∈T_j for some k≥1>>_U; set T_omega=∪T_j.
The union is normal. If a coset in U/T_omega has finite order, its power
lies in a finite T_j, hence its representative lies in T_{j+1}; so this
quotient is torsion free. Every map to a torsion-free group kills all T_j
by induction, since a root of an element in its kernel is again in its
kernel. Thus TFS for this input is equivalent to G∩T_omega(U)=1, or to
G∩T_j(U)=1 for every finite j. The radical and its universality are credited
to Brodsky–Howie and Chiodo 3.9–3.10. This round has not established the
displayed intersection assertion.

## A different full-scope construction: a torsion-free relation cover

There is a useful cover B=E/[N,N] with kernel M=N/[N,N] over U. Here is
the complete reason it is torsion free in the relative setting. The group E
acts on the free-product tree with vertex stabilizers conjugate to G and
trivial edge stabilizers. N meets every such stabilizer trivially, because
G embeds in U. Thus N acts freely on the tree and is free. A free action
on a tree gives a free group by choosing a spanning tree of the quotient
graph and lifting its other edges as generators. In particular M is free
abelian and torsion free.

Suppose b∈B has finite order and image u∈U. If u=1, b∈M and b=1.
Otherwise the finite cyclic subgroup <u> has preimage L≤E. Its intersection
with every conjugate of G is trivial: its image lies in a finite subgroup
of the torsion-free conjugate coefficient group, and q is injective there.
Hence L is free as well. A lift l∈L of b maps nontrivially to <u>, so its
class in L_ab is nonzero. But b^k=1 gives l^k∈[N,N]⊆[L,L], impossible
in the free abelian group L_ab. Thus B is torsion free and preserves G.
This classical abelianized-relation-cover operation is not proposed as novel.

It does not solve the equations: their values in B lie in M. Correcting them
while retaining their canonical images in U is an excessive requirement.
Indeed, if π:D→U lifts G and admits solutions d_j with π(d_j)=q(x_j),
the relator presentation gives s:U→D, with πs=id_U. Thus U embeds in D.
A torsion-free D could have these lifted solutions only if U were torsion
free. The allowed input x^2=1 over G=1 has U=C2 and disproves this proposed
universal lifting operation, while TFS is satisfied by x=1. Consequently
one must still change the image of U while preserving G.

Making the error kernel central also fails. This can be checked without
computations on presentations. Let E=F(a,b), r=a^2b^{-2}, s=b^{-1}aba,
and N=<<r,s>>. The exponent matrix [[2,-2],[2,0]] has determinant 4.
The quotient U is Q8: its relations give a^2=b^2, a^b=a^{-1}, hence
a^4=b^4=1 and at most eight forms a^i b^j; quaternion units realize all
eight. In C=E/[E,N], r,s are central, a^2=r b^2 commutes with b, and
a^b=s a^{-1}. Therefore a^4=s^2 and

    [a,b]=s a^{-2},                  [a,b]^2=1.

Its image in Q8 is -1, so this is nontrivial torsion in C. Thus the
torsion-freeness of the abelian cover cannot be carried over by centralizing
the module. This nonsingular input again has the solution a=b=1 in a
torsion-free group; it is a countercheck on a proposed method, not on TFS.
`relation-cover-checkpoint.md` supplies the normal-form details and limits.

## A full-scope universal-coefficient reduction

Chiodo 3.14 gives recursive universal torsion-free quotients; 2.2 gives
torsion-preserving Higman embedding; 4.9 supplies one fixed finitely presented
torsion-free group K containing every recursively presented torsion-free
group. These actual interfaces and the supporting quotient/universality
proofs were read. This does not imply every arbitrary group embeds in K.

Instead, every torsion-free G embeds in an ultrapower of K, as follows.
For any finite fragment D of the group diagram of G, present P_D using
symbols for its finitely many named elements and its finitely many equations.
The map P_D→G factors through P_D^tf. All inequations in D survive in
P_D^tf because they survive under this map to G. That quotient is recursively
presented: enumerate normal-closure power consequences, adjoin roots, and
dovetail all finite stages. Its torsion-freeness and universality follow
from the same finite-witness argument as for T_omega. It therefore embeds
in K. So every finite fragment, including its inequations, is realized in K.

Take an ultrafilter on the finite fragments containing all extensions of
each fixed fragment. Assign to each g its realized values where named and
1 elsewhere. Every multiplication equation holds on an ultrafilter-large
set, and every required inequation does too. This defines an embedding
G→K^I/𝒰. No enumeration or effectiveness of G is used, and I may have
arbitrary cardinality.

If all nonsingular systems over K have torsion-free solution overgroups,
the same holds over its ultrapowers: choose representatives of the finitely
many coefficients, solve the same exponent-matrix system coordinate by
coordinate over K, and take the ultraproduct of the solution groups. These
groups may be restricted to the countable subgroups generated by K and the
solution values, so the choices range over quotients of the fixed K*F_n. The
coefficient ultrapower embeds because every coordinate map is injective.
An ultraproduct is torsion free since a fixed power becoming 1 means that
power is 1 on a large set, hence its root is 1 there too. Restricting the
embedded coefficient group to G finishes the implication. Thus full TFS is
equivalent to solvability of ALL original finite nonsingular systems over
this one K. The converse is immediate. This credits and spells out the
quasivariety closure already supplied by KMR Proposition 2; it is not a
substantial nomination. No such theorem over K has been proved.

There is a concrete distinction from the earlier perfect locally-free limit.
K contains the familiar Higman four-cycle
J=<a,b,c,d | b^a=b^2,c^b=c^2,d^c=d^2,a^d=a^2>.
Here is an independent property check. The Baumslag–Solitar group
<b,c|c^b=c^2> is an HNN extension of Z, hence torsion free, with
<b>∩<c>=1. Adjoin a identifying <b> with <b^2>. Britton normal form
makes <a,c> free of rank two: a nonzero power of c lies in neither
associated subgroup. This three-generator group A is torsion free.
The analogous group B=<c,d,a|d^c=d^2,a^d=a^2> is torsion free with
<c,a> free. Their amalgam along these free subgroups is J. Cyclically
reduced normal form makes an element of finite order conjugate into a
vertex group, so J is torsion free and nontrivial. Abelianizing its four
relations kills each generator, so J is perfect. Thus J is a genuine
finitely generated, non-locally-free perfect subgroup of K. It is a known
test subgroup, not a TFS counterexample or a claim that J is simple.
Its image in any solvable group is perfect and solvable, hence trivial.
Residual-solvable detection therefore cannot separate all coefficients of K.
The detailed proof is in `universal-coefficient-checkpoint.md`.

## Recovered primary torsion-free-image theorem

The complete Brodsky–Howie paper was obtained from the publisher PDF at
https://link.springer.com/content/pdf/10.1007/BF02937335.pdf and read,
including all twenty printed pages. A rendered theorem page confirms that
the conclusion concerns the hatted universal torsion-free IMAGE; extraction
often loses the hat. Theorems 1.2–1.4 impose precise short-relator and
few-relator hypotheses. Corollary 1.5 uses complexity at most five.
Their Theorem 1.6 rules out a nontrivial coefficient witness expressed by
at most four conjugates of a one-relator product's defining relator.

Its proof's radical operation differs from the desired one. It forms abstract
coefficient presentations A0,B0 from the regions of a minimal spherical
picture. Their maps into the original torsion-free factors factor through
their universal torsion-free images. For n≤4 relator vertices, Euler's formula
Σ(k-2)F_k=2n-4 bounds the region-presentation complexity tightly enough for
the small-presentation theorem. It does not prove that an arbitrary original
coefficient subgroup survives the torsion-free image of U. Full row rank
gives no bound n≤4 or complexity≤5. No new argument imposing that bound
on an arbitrary finite radical certificate was found. This primary reading
pays the previously missing retrieval, not the full preservation operation.
`primary-operation-checkpoint.md` records exact interfaces and limitations.

## Preserved objections and final unpaid operation

The r13 torsion tower P=<x,y,z|x^2,y^3,xy=z^6> remains a real nonsingular
input G*P with a trivial-variable torsion-free solution. Treating z as a
coefficient gives three equations in two unknowns and stays outside scope.
Every adjoined root consequence has exponent vector in the original rational
row span: apply the exponent homomorphism to a finite normal-closure power
witness and divide its exponent vector by the power. Induction proves this
at every radical stage. Thus simply reapplying the full-rank theorem still
fails, without proving that coefficients are lost.

Rational abelianization and KMR residual detection remain paid and insufficient
for all G. Smith form does not layer words. The source Proposition 4.1 still
requires coefficient-only boundaries and every variable slot paired; variable
power boundaries do not satisfy its balance hypotheses. Forester–Rourke
requires actual layering/unimodularity. Ramirez-Côté–Wise requires the stated
power-series embeddings; the new relative cover is not such an embedding.
The earlier perfect direct limit is locally free and not a hard example for
finite equations. No blanket statement about all real-degree filtrations is
made. Finitely generated coefficient and square-system reductions remain
valid paid operations; the new universal reduction proves its extra closure
steps instead of quietly dropping ineffective groups. Covering transfer and
arbitrary independent-system extensions are not claimed anew.

**Still unpaid:** for every frozen input, prove G∩T_j(U)=1 for every finite
j, or exhibit an actual input and a nonidentity coefficient in that
intersection. Equivalently the universal coefficient K must admit all the
specified torsion-free solutions; this was not established. Neither a
torsion-free cover of U nor local indicability of a small abstract image
provides that missing operation. No full argument or counterexample emerged.

The package authenticates the frozen r13 tree against its supplied seal and
binds its two historical references and two pinned Git identities. Mutable
parent context is snapshotted internally. The final verifier is read only;
it checks exact membership, sizes, SHA256 and Git blob identities, and source
immutability. Its acceptance is integrity only, not mathematical or contribution
acceptance. No mathematical scans or third-party research code ran. All new
writes are confined to this directory; no nested agents, staging, commits,
external messages, uploads, publication, submission, manuscript or Lean work
occurred. Analytic r12 and crossing manuscript work were not duplicated.
