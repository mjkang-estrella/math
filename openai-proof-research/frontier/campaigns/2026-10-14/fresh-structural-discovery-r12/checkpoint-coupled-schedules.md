# Q4 checkpoint: two schedules with a free junction

Put (a,b,c,d)=(lambda1,...,lambda4). The first schedule starts at a,
moves along the straight shape tb, and ends at a Weyl representative z
of the intermediate weight. Rotate the second schedule so it starts at
that SAME z; it moves along tc and ends in W(d*). The source basic-schedule
and schedule-moment interfaces permit at most n switches in each segment.
No assertion that their concatenation is a single source schedule is made.

Fix root lists beta_1,...,beta_k and delta_1,...,delta_l (k,l<=n),
initial direction frames u,v, and final endpoint frame r. Define
 u_i=s_beta_i ... s_beta_1 u, v_j=s_delta_j ... s_delta_1 v,
 C_i=-beta_i . u_(i-1)b, D_j=-delta_j . v_(j-1)c.
Delete zero-total switches. Thus C_i,D_j are POSITIVE integers.
Let x_i and y_j be switch coefficients. For straight shapes, times are
x_i/C_i and y_j/D_j. The exact feasibility equations/inequalities are

 0 <= x_1/C_1 <= ... <= x_k/C_k <= 1,
 0 <= y_1/D_1 <= ... <= y_l/D_l <= 1,
 z=a+u_k b-sum_i x_i beta_i,
 z+v_l c-sum_j y_j delta_j = r d*,
 beta_i.a - sum_(h<i) x_h beta_h.beta_i - x_i >= 0,
 delta_j.z - sum_(h<j) y_h delta_h.delta_j - y_j >= 0.

For an empty root list its time inequalities are omitted and its final
frame is its initial frame. All coefficients are rational (indeed integral
after clearing the positive C,D denominators). The listed x,y ranges are
bounded. Hence each fixed combinatorial choice gives a rational polytope.
There are finitely many root lists, frames and lengths for each n.

Proof of faithfulness: set each time to its displayed ratio and successively
integrate the constant Weyl-translated velocities. Induction through the
reflection identities gives y(t)=initial+w(t)shape(t)-sum(previous m roots).
Its beta_i gap is exactly the displayed expression, because
beta_i.u_(i-1)shape(time)=-x_i. The endpoint and weak time order therefore
give precisely source schedules. Conversely any such two schedules obey
these same equations. Coincident times retain their indicated order. A
Weyl rotation making z dominant turns the second one into the ordinary
source interface with a dominant initial label and end orbit W(d*).

Summing the endpoints removes the unknown junction:
 sum_i x_i beta_i+sum_j y_j delta_j = a+u_k b+v_l c-r d* in Q.
The last membership follows from total external root congruence and
Weyl action being trivial on P/Q. This pays an integral right-hand side,
NOT integral solvability with the inequalities. Integer x,y would give
z in a+b+Q, and would suffice via rational moment/occurrence and the
stipulated triple theorem. Requiring all x,y integral is stronger than
necessary: only z in that coset is the exact target.

The source one-segment continuation cannot be applied unchanged. It uses
one common shape, a fixed total moving weight and its one Bruhat order.
At this free junction the direction can RESET. Treating it as an ordinary
shape break would imply moment feasibility for (a,b+c,d*), which is false
for the actual Cartan-replacement example in checkpoint-diagonal.md.
Global root balancing does not pay the missing two-segment continuation.
