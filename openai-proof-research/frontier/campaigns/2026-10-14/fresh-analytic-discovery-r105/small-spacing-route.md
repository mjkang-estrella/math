# Small-spacing vertical alternative: exact tradeoff and multi-branch issue

This tests a different vertical geometry after the source-hierarchy peak obstruction. It does not change the frozen target.

## 1. Rectangular Gaussian budget cannot retain only adjacent pairs

Take vertical lattice h Z^D, with normalized zero-atom weight A=(h/sqrt(2pi))^D. The two adjacent integer choices in each coordinate retain normalized Gaussian mass

 F_h(t)=product_(j=1)^D [h gamma_1(h t_j)+h gamma_1(h(t_j-1))], t in[0,1]^D.

Its cube average is a(h)^D, a(h)=P(|Z|<=h)<1. Thus there exists a target with F_h(t)<=a(h)^D. If a sequence h_D obeys A<=C for fixed C, then h_D<=sqrt(2pi) C^(1/D). Consequently limsup a(h_D)<=a(sqrt(2pi))<1, and inf_t F_h(t) decays exponentially in D. Conversely any uniform positive lower bound on F_h(t) forces a(h_D)^D bounded below, hence h_D->infinity, and then A diverges superexponentially relative to a fixed base.

This exact argument excludes the simplest dense rectangular replacement WITH ONLY adjacent binary patterns. It neither excludes nonrectangular lattices nor a construction retaining more integers per coordinate. Here A is a single normalized atom, so its obstruction is already sufficient before periodizing all Gaussian weights.

## 2. Why replacing two siblings by many siblings changes the shear estimate

The source shear proof uses exactly TWO translates A and B+z, whose expected intersection is |A||B|. For q>=3 siblings in arithmetic progression, a common Haar z gives dependencies.

On R/Z let U=[0,eta] with 0<eta<1/2. For 0<=z<=eta/(2q) and x in[eta/2,eta], every x-jz, j=0,...,q-1, lies in U. Therefore

 E_z |intersection_(j=0)^(q-1) (U+jz)| >= eta^2/(4q).

For any fixed q>=3 the ratio to eta^q tends to infinity as eta->0. Thus no constant depending only on q can replace this expectation by C_q eta^q for arbitrary hole sets. In the source regime eta=exp(-u/2), this is an exponential loss in u, not a harmless combinatorial pattern count. The inequality is a lower bound on the RANDOM SHEAR expectation; it does NOT rule out some exceptionally good deterministic z. Indeed intervals can be separated by suitable z. It blocks the independent-product averaging proof, not existence.

## 3. Two remaining possible interfaces

(a) A multi-branch shear theorem using geometric structure of actual convex-section hole sets, stronger than the arbitrary-measurable-set lemma. The source only supplies their measures; no such additional structure was proved in this attempt.

(b) A different higher-rank lattice construction that supplies independent shifts for sufficiently many section copies while keeping one lattice and total density O(n log n). Introducing arbitrary independent shifts gives a finite union of cosets, which is excluded by the full target. Enlarging the generated subgroup generally adds many unwanted centers and cannot be done without counting them.

Lund's primary Section4 and Section5 were read fully at their operative ranges. Its arbitrary-subset hashing counterexample already rules out a universal o(n^2) mean guarantee in the standard p~n, kernel dimension~n/log n discretization. That is not a counterexample for discretized convex bodies and not a lower bound on our target. It prevents bypassing (a)/(b) merely by asserting better hashing for all finite subsets.
