# Cubic torus phases: supporting screen, no target

These are prefreeze feasibility calculations, not a new theorem nomination. The source supplies the complete profile and all equality cases. The numerical transitions themselves are not discoveries.

On the unit cubic three-torus put, for volume v<=1/2,

    P_B(v)=(36 pi)^(1/3)v^(2/3),
    P_T(v)=2 sqrt(pi v),   P_S(v)=2.

The pinned [source354 paper](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex), `intro:main`, gives I(v)=min(P_B,P_T,P_S), the exact classes and complement rule. At v_1=4pi/81 the sphere radius is1/3 and the tube radius2/9. Their common perimeter is4pi/9. Their volume derivatives are6 and9/2, respectively. At v_2=1/pi the tube radius is1/pi, its derivative is pi, and the slab derivative is0. The transitions are transverse crossings of distinct smooth branches.

For the sphere, the constrained perimeter Jacobi eigenvalues are [l(l+1)-2]/R^2. The constant l=0 mode is removed by the volume constraint; l=1 comprises translations; the remaining gap is4/R^2. For a length-one circular tube the eigenvalues are

    lambda_(m,j)=(m^2-1)/r^2+4pi^2 j^2,  m,j integers.

The constant mode is removed by volume, and (m,j)=(+/-1,0) are translations. For r in [2/9,1/pi] every other mode is bounded below by min(4pi^2-81/4,3pi^2)>0. For a slab, the two boundary components are flat unit two-tori; after the volume constraint and common translation are removed, the next eigenvalue is4pi^2. Hence a phase crossing does not itself produce a zero Jacobi mode within one phase.

[Acerbi–Fusco–Morini, arXiv:1211.0164v1](https://arxiv.org/pdf/1211.0164v1), Theorem1.1, supplies quadratic L1 local minimality modulo translations from strictly positive second variation, including gamma=0. Its closing penalization argument was read. Applying it to these fixed smooth regions is the existing compatible reduction; its earlier regularity inputs were not independently reconstructed. No new stability theorem is claimed.

One tempting uniform formulation fails for a simple reason. Immediately to the right of v_1, a ball of the required volume has positive deficit P_B-P_T=(3/2)(v-v_1)+O((v-v_1)^2), tending to zero. Yet its L1 distance from all minimizing tubes stays bounded below as v decreases to v_1. Otherwise compactness of translations and the finite axis choices would identify a ball and a wrapping tube at the transition, impossible for their open interiors. Immediately below v_1 the tube gives the reversed example. At v_2 the same argument uses tube/slab and a linear gap with coefficient pi. Thus one cannot have a positive all-volume constant controlling squared distance to only the exact minimizing class on both sides of either crossing. This does not refute fixed-volume stability or an appropriate multi-phase estimate.

A replacement using every nearby phase would combine the source classification, compactness and the existing local theorem, with a separate uniformity check. No such replacement is nominated. Prior I346 already contains substantive morphology/crossover work; its source/profile and comparison portions were encountered in the body search, not cleared by absence of an identical title. Its complete singular crossover proof was not reread here. No priority claim follows from this calculation.
