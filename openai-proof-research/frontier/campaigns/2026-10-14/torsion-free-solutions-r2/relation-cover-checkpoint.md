# Checkpoint: a torsion-free cover, and why lifting its universal solution fails

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Fix EVERY original input. Write E=G*F_n, N=<<w_i>>_E, U=E/N and q:E→U.
The stipulated theorem says q|G is injective. Define

    M=N/[N,N],                 B=E/[N,N].

The free abelianized extension is a classical construction, not proposed as
novel. The free-presentation interface appears in Evans, *Relation modules of
infinite groups*, introduction, equations (1)–(2). Below we prove the relative
version actually needed instead of treating a free E as if it were G*F_n.

## A complete torsion-freeness proof

Use the Bass–Serre tree of the graph of groups with one vertex group G and n
loop edges with trivial edge groups. Equivalently, its vertices are left cosets
E/G, and an edge labelled j joins eG to ex_jG, with the usual distinct edge
cosets. Reduced free-product words prove this is a tree; vertex stabilizers
are conjugates of G and edge stabilizers are trivial. A group acting freely
on a tree is free: choose a maximal tree in the quotient graph, lift it, and
use the remaining oriented edges as a free basis. The usual reduced path
normal form proves absence of relations. These facts allow arbitrary ranks.

The subgroup N acts freely because N∩eGe^{-1}=1 by coefficient injectivity.
Thus N is free, and M is free abelian, in particular torsion free.

Suppose b in B has finite order and let u be its image in U. If u=1 then
b∈M, hence b=1. Otherwise let d>1 be the order of u and put
L=q^{-1}(<u>). For each e, the image of L∩eGe^{-1} lies in the intersection
of the finite cyclic group <u> and the torsion-free group q(eGe^{-1}). That
intersection is trivial. Since q is injective on eGe^{-1}, the original
intersection is trivial as well. Thus L acts freely on the tree and is free.

Choose l∈L lifting b. The map L→<u> sends l to a nonidentity element. Because
<u> is abelian, l has nonzero image in L_ab. But b^k=1 gives l^k∈[N,N],
which is contained in [L,L]. Hence k[l]=0 in the free abelian group L_ab,
a contradiction. Therefore B is torsion free. G embeds in B because the
kernel [N,N] is contained in N. We have constructed, for ALL original inputs,

    1 → M → B → U → 1

with B torsion free and G preserved. No claim that the w_i vanish in B follows:
their values are in M and are generally nonzero.

## The proposed correction operation is too strong

Suppose more generally that π:D→U is any group epimorphism, there is an
embedding j:G→D lifting q|G, and there are d_j with π(d_j)=q(x_j) satisfying
all w_i(j(G),d_1,...,d_n)=1. The presentation universal property gives a map
s:U→D with s|G=j and s(q(x_j))=d_j. The composite πs fixes all generating
elements of U, so πs=id_U. Consequently s is injective. If D is torsion free,
U must be torsion free too.

This rules out a universal strategy that corrects the lifts within a fixed
cover of U. The allowed input G=1, w=x^2 has U=C2 and already makes such a
strategy impossible. TFS nevertheless holds for that input by x=1. A valid
TFS construction is allowed, and sometimes required, to change the image of
the universal group. The failure of this lift is not failure of TFS.

## Centralizing the kernel does not repair the construction

Here is a direct two-equation calculation. Set G=1, E=F(a,b),

    r=a^2 b^{-2},             s=b^{-1} a b a,
    N=<<r,s>>,
    A=[[2,-2],[2,0]],         det A=4.

U is Q8. Indeed b^{-1}ab=a^{-1} and a^2=b^2 imply a^4=b^4=1;
every word reduces to a^i b^j with 0≤i<4 and 0≤j<2. Sending a,b to
the quaternion units i,j satisfies the relations and gives eight distinct
images, proving the presentation has precisely this group.

In C=E/[E,N], the elements r,s are central. The equality a^2=r b^2 makes
a^2 commute with b. With a^b=b^{-1}ab=s a^{-1}, it follows that

    a^2=(a^2)^b=s^2 a^{-2},              a^4=s^2.

For z=[a,b]=a^{-1}b^{-1}ab=s a^{-2}, therefore z^2=1. Its image in Q8
is -1, so z≠1 in C. Thus C has actual torsion. This calculation uses no
enumeration software or assumed structure theorem for central extensions.
The abelian kernel M of B cannot simply be made central while retaining
torsion-freeness. Again the original system has the torsion-free solution
a=b=1; this is no TFS counterexample.

## Precise disposition of the attempted proof

The normal-form construction pays a torsion-free relative cover, not a
torsion-free image solving the relators. Correcting over the same base U
would pay the unnecessarily stronger and false demand U↪D. Centralizing
the error module can itself introduce torsion. No coefficient-preserving
change of base U→V was constructed. The exact missing operation remains
G∩T_omega(U)=1, with every original word and invariant factor retained.
