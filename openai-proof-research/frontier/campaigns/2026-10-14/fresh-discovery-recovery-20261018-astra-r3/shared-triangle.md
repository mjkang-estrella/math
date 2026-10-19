# An exactly solvable shared-triangle model

This finite three-resource model isolates the correction lost by independent root lists. It is not claimed to represent the complete finite continuation: actual external subtrees can overlap, and their lifetimes are then dependent. The derivation is self-contained and does not use a numerical approximation.

Let L_1,L_2,L_3 be independent random variables taking values in (0,infinity], independent of U uniform on [0,1]. Resource i is removed externally at time L_i. The central triangle is tested at time U and removes all three resources if U<min_i L_i. Let Y_i indicate survival of resource i at time 1. Define

    a_i=P(L_i>1), c_i(t)=P(L_i>t) for 0<=t<=1,
    J_i=integral_0^1 c_i(t) dt,
    J_ij=integral_0^1 c_i(t)c_j(t) dt.

Any atoms at time 1 can be avoided by assuming P(L_i=1)=0; atoms elsewhere are permitted, since U has a continuous law. The exact formulas are

    E Y_i = a_i (1-J_jk),
    E Y_i Y_j = a_i a_j (1-J_k),
    E Y_1 Y_2 Y_3 = 0.                                      (1)

For the first formula, external survival of i is independent of U,L_j,L_k. Conditional on it, central acceptance has probability integral c_j c_k. For the second, condition on both external survivals; central acceptance has probability integral c_k. For the third, if every external lifetime exceeds one, the central triangle is accepted almost surely by time one. These arguments prove (1) for every admitted law, not just the examples checked computationally.

Thus

    Cov(Y_i,Y_j)=a_i a_j [J_ik+J_jk-J_ik J_jk-J_k].            (2)

For identical laws write a_i=a, c_i=c, J_ij=J2 and J_i=J1. Then

    Cov(Y_1,Y_2)=a^2(2J2-J2^2-J1),
    E product_{i=1}^3(Y_i-m)
      =a^3(1-J2)[-3(1-J1)+2(1-J2)^2], m=a(1-J2).            (3)

The second expression follows by expanding the product and using E Y_1Y_2Y_3=0, the three identical pair moments and E Y_i=m. It is the third joint cumulant as well.

Choose the source-shaped exterior tail c(t)=(1+2Dt)^(-1/2) on [0,1], for any real D>0. This is a valid lifetime distribution: its continuous density on (0,1) is D(1+2Dt)^(-3/2), with the remaining mass a=(1+2D)^(-1/2) placed at L=2. Direct integration yields

    J1=(sqrt(1+2D)-1)/D=2a/(1+a),
    J2=log(1+2D)/(2D)=-2a^2 log(a)/(1-a^2).

As D tends to infinity, a tends to zero, J1/a tends to2, J2/a tends to0 and J2 tends to0. Consequently

    Cov(Y_1,Y_2)/a^3 -> -2,
    E product_{i=1}^3(Y_i-m)/a^3 -> -1.                      (4)

The limits use the elementary fact a log(1/a)->0. They are not extrapolated from finite diagnostics. The actual single-root marginal is m, asymptotic to a.

These corrections explain why retaining a shared triangle can matter even though an independent branch approximation gets each one-root marginal right to relative o(1). They also caution against assigning one independent small factor to every pair of a collision graph: a single shared three-resource constraint produces a third centered moment at the same a^3 scale as its pair covariance. For T188U the initial star has only two edges from any one triangle, so (4) is not itself a claimed six-star-root contribution; descendants introduce additional resources. No variance constant, CLT, all-vertex bound, or finite-process independence is inferred.
