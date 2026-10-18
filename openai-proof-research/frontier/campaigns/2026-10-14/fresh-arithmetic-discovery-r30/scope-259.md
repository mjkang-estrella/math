# Frozen scope T259S: distinct costs among spectral-gap actions

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Frozen at 2026-10-18T06:25:44.803736+00:00 after the quotient-collapse mechanism was discovered and communicated to the parent, and before writing/verifying the complete measurable graphing proof or completing the primary comparison. The informal mechanism already included the expected cost-one and spectral-gap conclusions; this is not a claim that no mathematical reasoning preceded the freeze. No earlier full259 target was frozen in r30. Prior262/095 and other catalogue screens are not nominees.

Let A=F(a,b_1,...,b_99), u_0=1, u_i=u_(i−1) a b_i, w=u_99 a, J=<b_1,...,b_99,w>, and

    Γ=A *_J (J×<t>).

Let F=F(c,d) and define q:Γ→F by

    q(a)=d, q(t)=1,
    q(u_1)=c, q(u_i)=1 for 2≤i≤99.

Equivalently q(b_1)=d^−1 c, q(b_2)=d^−1 c^−1, and q(b_i)=d^−1 for3≤i≤99. Thus q(w)=d. This is part of the claimed construction and will be justified from the free-basis change and the amalgam relations.

On X=[0,1]^Γ and Z=[0,1]^F use product Lebesgue probability and the right Bernoulli convention (xg)(h)=x(gh). Define the explicit diagonal Γ-action on Y=X×Z by

    (x,z)g=(xg,z q(g)).

The frozen theorem claims ALL of the following:

1. Γ is finitely presented, and q is a well-defined surjective homomorphism. The action on Y is essentially free, probability preserving, and weakly mixing.
2. Its full orbit-equivalence-relation cost is exactly1. This means for every epsilon>0 there is a countable measure-preserving Borel graphing generating the complete Γ-orbit relation modulo null sets with total domain measure below1+epsilon. No partial-relation or finite-level substitute is allowed.
3. For every complex f∈L²(Y) of mean zero,

       ||f(·w)−f||²_2+||f(·b_1)−f||²_2
         ≥(4−2sqrt(3))||f||²_2.

   In particular the Γ-action has spectral gap and is strongly ergodic.
4. The Γ-Bernoulli action on X is also essentially free, weakly mixing and has spectral gap, while its cost is at least1+eta for any source-admissible eta=alpha/100>0 (0<alpha<1/200 and e^96 96^99 alpha^3/95^95<1/2). Thus the same explicit finitely presented group has two essentially free weakly mixing spectral-gap p.m.p. actions of different costs.

No mixing claim is made for Y: the infinite kernel of q fixes its Z-factor. No assertion about all actions of Γ, universal cost interpolation, a fixed-price classification, or an abstract minimum-cost strong-ergodicity theorem is included. These exclusions clarify the constructed existence theorem; they do not modify a previously frozen broader target.

Pinned dependency: source259 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, with its theorem truth stipulated. The lower bound on Bernoulli cost and the source's B-marker operation are credited inputs. Root's previous profinite-height cost-one transfer remains technical and unchanged. The proposed unpaid operation is a nonamenable quotient with exactly one exceptional row coordinate, enabling marker propagation while a free rank-two subgroup retains Bernoulli spectral gap. Contribution eligibility remains subject to actual primary comparison and independent gates. No acceptance or count change is made.
