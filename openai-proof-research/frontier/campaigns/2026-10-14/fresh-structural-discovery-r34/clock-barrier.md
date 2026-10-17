# A finite-clock obstruction and genuine unbounded exceptional runs

This proves a limited diagnostic consequence of the stipulated height-three construction. It neither disproves the full height-two question nor supplies a new accepted result.

## 1. Abstract counting statement

Let H be a finite abelian group and Lambda a set of m >= 2 tags. Let I_alpha,J_alpha be subsets of H. Put

    E_z = {(alpha,lambda): z in I_alpha + J_lambda}.

Assume each E_z is either contained in the diagonal or consists of a single off-diagonal pair. Let B be any nonempty subset of H on which E_z is the full diagonal, and put W=H minus B. Write a_alpha=|I_alpha|, b_alpha=|J_alpha| and b=|B|.

For every alpha, B is contained in I_alpha+J_alpha, hence a_alpha b_alpha >= b and both sets are nonempty. For alpha != lambda, the sumset I_alpha+J_lambda lies in W. These ordered off-diagonal sumsets are pairwise disjoint: a point in two would give two off-diagonal edges. Translation by one fixed element of either nonempty summand injects the other into the sumset, so

    |I_alpha+J_lambda| >= max(a_alpha,b_lambda).

Adding the disjoint cardinalities and applying the arithmetic-geometric mean inequality yields

    |W| >= sum_(alpha != lambda) max(a_alpha,b_lambda)
         >= (m-1)/2 sum_alpha (a_alpha+b_alpha)
         >= (m-1) sum_alpha sqrt(a_alpha b_alpha)
         >= m(m-1) sqrt(b).

In particular, an off-diagonal total exists. The last existence assertion also follows directly by selecting elements from I_alpha and J_lambda for two distinct tags. The squared bound |W|^2 >= m^2(m-1)^2 |B| avoids radicals. No assertion about a uniform positive exceptional density as |H| grows follows from this estimate.

## 2. Applying the statement to the actual source clock

Use the height-three manuscript's `clock:robust`, `schedule:copies`, `schedule:clock-roster`, and `schedule:final-net`. Let H=phi(Z), the finite cyclic image of the final periodic clock, and restrict each torus set I_alpha,J_alpha to H. Let B=H minus W_torus and W_H=H intersect W_torus.

For z in B the source supplies a radius-rho ball in I_alpha intersect (z-J_alpha), for every tag. The finite net {phi(aB_schedule):0 <= a < R} lies in H and has covering radius strictly below rho. It meets that ball. If i is such a point, j=z-i also belongs to H and J_alpha. Thus the **restricted** finite-clock graph is the full diagonal at z. Its graph at every other z is still contained in the source graph, so the edge alternative persists.

B is nonempty. The roster has N=kappa*mu slots with kappa >= 1, and mu > 20*c_cl*log(2m)+10. In particular N(N-1)>c_cl*log(2m). Apply the roster estimate at translate zero. At least one ordered distinct-slot difference phi(p')-phi(p), which belongs to H, is outside W_torus. The set B therefore contains a point. The tag formula in `schedule:choices` gives m >= 2 (indeed |V| >= 2, with all input/output fields present).

All hypotheses of section 1 hold, and the counting inequality follows for W_H. Select distinct tags alpha,lambda and choose i in I_alpha intersect H, j in J_lambda intersect H, possible by the good-total argument. The total h=i+j has the off-diagonal edge (alpha,lambda); the source graph alternative makes that its **unique** edge. In particular h is exceptional.

## 3. Realizing this total by complete episodes

Fix any original alphabet containing distinct letters a,b. All construction parameters and cut schedules are now fixed. The true origin for a word starting at zero is t=L. Choose q so large that every bounded inspection window and seed used at this true origin to define the episode, its inner marker searches, its end searches, and their fixed stability translates lies strictly before q. This is possible because the collection is finite. Also choose q beyond the end seed's right endpoint. If desired, enlarge this threshold to cover every false-origin window in the source's finite margin list; nothing in the argument changes.

Let n be a positive period of phi. Since h is in H, choose an integer r with phi(r)=h and impose q=L+r modulo n. There are arbitrarily large such q. Define e_q=a^q b a^(L_tail-1).

No marker is placed in the inspected constant region: the priority rule in `marker:local` considers only length-K words with no period below d, whereas every inspected constant a-word has period one. The same reasoning applies separately to inner and end markers. Thus the true smaller and larger end searches eta(t),zeta(t) are absent; all required seeds are constant a-words. The seed continuation is the two-sided constant a-word. Its first mismatch at or after the seed is the letter b at position q. By `episode:endpoint`, e_q has exactly the required endpoint q+L_tail, and all mandatory windows are present. It is a complete episode.

Since zeta(t) is absent, its actual clock anchor is q, so phi(q-t)=h. The off-diagonal edge implies h in W_torus: outside that set the graph is the full diagonal. Therefore A_*(t,q) holds and e_q belongs to D, irrespective of the other disjuncts.

For any accepted outer split of e_q with incoming state x, `episode:shared-end` forces its actual endpoint and clock anchor even when the two tags were independently chosen. The two clock tests then put those tags in E_h. Uniqueness of E_h forces the prefix tag to be alpha and the suffix tag to be lambda. The prefix definition forces x=X(alpha). Pick any x' in V different from X(alpha), possible because |V| >= 2. There is no successful outer split of e_q with input x'. This is the exact failure of outer completeness, rather than merely the presence of an exceptional label.

Finally E is a prefix code by `episode:prefix-code`. For every k>=1, the word e_q^k is an E*-word whose unique episode parsing consists of k copies of e_q, all in D. Translation invariance and internal windows keep the episode data unchanged in each copy. Thus exceptional runs have no finite bound. These words are genuine source instances, not an abstract clock countermodel.

The argument uses two distinct letters solely to demonstrate a barrier within the unchanged all-finite-alphabet target. Unary and empty alphabets are not removed from that target. This is not a lower-bound argument for the languages recognized on these particular words.
